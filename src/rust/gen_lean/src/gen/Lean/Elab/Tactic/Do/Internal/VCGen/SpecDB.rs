// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB
// Imports: Lean.Elab.Tactic.Do.Attr Lean.Meta.Sym.Pattern Lean.Meta.DiscrTree.Util Lean.Meta.Sym.Simp.DiscrTree Lean.Meta.Sym.Util
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget_borrowed, lean_expr_eqv, lean_expr_lift_loose_bvars, lean_infer_type,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr,
    lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_lor, lean_uint64_of_nat, lean_uint64_shift_left, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop, l_Array_append___redArg,
    l_Array_ofFn___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr4};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Attr::{
    initialize_Lean_Elab_Tactic_Do_Attr, l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof,
    l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate,
    l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key,
    l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin,
    l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred,
    l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq,
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default,
    runtime_initialize_Lean_Elab_Tactic_Do_Attr,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getForallBody,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_isForall,
    l_Lean_mkAppN, l_Lean_mkBVar, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkCongrFun;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_forallMetaBoundedTelescope, l_Lean_Meta_forallMetaTelescope, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_empty, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::DiscrTree::Util::{
    initialize_Lean_Meta_DiscrTree_Util, runtime_initialize_Lean_Meta_DiscrTree_Util,
};
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_getEqnsFor_x3f;
use crate::r#gen::Lean::Meta::Sym::Pattern::{
    initialize_Lean_Meta_Sym_Pattern,
    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go,
    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern,
    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern,
    l_Lean_Meta_Sym_Pattern_match_x3f, l_Lean_Meta_Sym_instInhabitedPattern_default,
    runtime_initialize_Lean_Meta_Sym_Pattern,
};
use crate::r#gen::Lean::Meta::Sym::Simp::DiscrTree::{
    initialize_Lean_Meta_Sym_Simp_DiscrTree, l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys,
    l_Lean_Meta_Sym_getMatch___redArg, runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::l_Lean_Meta_simpGlobalConfig;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0_value:
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
    m_data: [69, 113, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__0_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2: u64 = 0;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 84, 114, 105, 112, 108, 101, 32, 0]};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [68, 111, 0]};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 114, 105, 112, 108, 101, 0]};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject,7300584325018775040 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject,11963640885769744415 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0_value:
    leanh::LeanStringObject<71> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 71,
    m_capacity: 71,
    m_length: 70,
    m_data: [
        32, 119, 97, 115, 32, 110, 111, 116, 32, 97, 32, 84, 114, 105, 112, 108, 101, 46, 32, 83,
        104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 104, 97, 112, 112, 101, 110, 32, 119, 105,
        116, 104, 32, 116, 104, 101, 32, 112, 114, 101, 118, 105, 111, 117, 115, 32, 116, 101, 115,
        116, 115, 32, 105, 110, 32, 112, 108, 97, 99, 101, 46, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2_value:
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
    m_data: [80, 111, 115, 116, 83, 104, 97, 112, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3_value:
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
    m_data: [97, 114, 103, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 0]};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [118, 99, 103, 101, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__0_value) as *mut leanh::LeanObject,12843180897352504333 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__1_value) as *mut leanh::LeanObject,17186385980065365684 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject,6272605754531080404 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__2_value) as *mut leanh::LeanObject,15978311213600074545 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__4_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 109, 105, 103, 114, 97, 116, 101, 32, 115, 105, 109, 112, 32, 115, 112, 101, 99, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0 as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 109, 105, 103, 114, 97, 116, 101, 32, 115, 112, 101, 99, 32, 116, 104, 101, 111, 114, 101, 109, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 103, 108, 111, 98, 97, 108, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 108, 111, 99, 97, 108, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [83, 112, 101, 99, 80, 114, 111, 111, 102, 46, 115, 116, 120, 32, 95, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0_value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 109, 105, 103, 114, 97, 116, 101, 32, 117, 110, 102, 111, 108, 100, 32, 115, 112, 101, 99, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__0
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__2
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__3_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__4
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx(
    mut v_x_3055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3055_) == 0 {
        let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3056_ = leanh::lean_unsigned_to_nat(0);
        return v___x_3056_;
    } else {
        let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3057_ = leanh::lean_unsigned_to_nat(1);
        return v___x_3057_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx___boxed(
    mut v_x_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorIdx(v_x_3058_);
    leanh::lean_dec_ref(v_x_3058_);
    return v_res_3059_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(
    mut v_t_3060_: *mut leanh::LeanObject,
    mut v_k_3061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_etaPotential_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_etaPotential_3062_ = leanh::lean_ctor_get(v_t_3060_, 0);
    leanh::lean_inc(v_etaPotential_3062_);
    leanh::lean_dec_ref(v_t_3060_);
    v___x_3063_ = leanh::lean_apply_1(v_k_3061_, v_etaPotential_3062_);
    return v___x_3063_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim(
    mut v_motive_3064_: *mut leanh::LeanObject,
    mut v_ctorIdx_3065_: *mut leanh::LeanObject,
    mut v_t_3066_: *mut leanh::LeanObject,
    mut v_h_3067_: *mut leanh::LeanObject,
    mut v_k_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3069_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3066_, v_k_3068_);
    return v___x_3069_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___boxed(
    mut v_motive_3070_: *mut leanh::LeanObject,
    mut v_ctorIdx_3071_: *mut leanh::LeanObject,
    mut v_t_3072_: *mut leanh::LeanObject,
    mut v_h_3073_: *mut leanh::LeanObject,
    mut v_k_3074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3075_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim(
        v_motive_3070_,
        v_ctorIdx_3071_,
        v_t_3072_,
        v_h_3073_,
        v_k_3074_,
    );
    leanh::lean_dec(v_ctorIdx_3071_);
    return v_res_3075_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_triple_elim___redArg(
    mut v_t_3076_: *mut leanh::LeanObject,
    mut v_triple_3077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3078_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3076_, v_triple_3077_);
    return v___x_3078_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_triple_elim(
    mut v_motive_3079_: *mut leanh::LeanObject,
    mut v_t_3080_: *mut leanh::LeanObject,
    mut v_h_3081_: *mut leanh::LeanObject,
    mut v_triple_3082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3083_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3080_, v_triple_3082_);
    return v___x_3083_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_simp_elim___redArg(
    mut v_t_3084_: *mut leanh::LeanObject,
    mut v_simp_3085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3086_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3084_, v_simp_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_simp_elim(
    mut v_motive_3087_: *mut leanh::LeanObject,
    mut v_t_3088_: *mut leanh::LeanObject,
    mut v_h_3089_: *mut leanh::LeanObject,
    mut v_simp_3090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3091_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremKind_ctorElim___redArg(v_t_3088_, v_simp_3090_);
    return v___x_3091_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3096_ = leanh::lean_unsigned_to_nat(1000);
    v___x_3097_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremKind_default;
    v___x_3098_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecProof_default;
    v___x_3099_ = l_Lean_Meta_Sym_instInhabitedPattern_default;
    v___x_3100_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3100_, 0, v___x_3099_);
    leanh::lean_ctor_set(v___x_3100_, 1, v___x_3098_);
    leanh::lean_ctor_set(v___x_3100_, 2, v___x_3097_);
    leanh::lean_ctor_set(v___x_3100_, 3, v___x_3096_);
    return v___x_3100_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default()
-> *mut leanh::LeanObject {
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3101_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default___closed__0,
    );
    return v___x_3101_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew()
-> *mut leanh::LeanObject {
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default;
    return v___x_3102_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0(
    mut v_thm_u2081_3103_: *mut leanh::LeanObject,
    mut v_thm_u2082_3104_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_proof_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    v_proof_3105_ = leanh::lean_ctor_get(v_thm_u2081_3103_, 1);
    leanh::lean_inc_ref(v_proof_3105_);
    leanh::lean_dec_ref(v_thm_u2081_3103_);
    v_proof_3106_ = leanh::lean_ctor_get(v_thm_u2082_3104_, 1);
    leanh::lean_inc_ref(v_proof_3106_);
    leanh::lean_dec_ref(v_thm_u2082_3104_);
    v___x_3107_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_proof_3105_, v_proof_3106_);
    return v___x_3107_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0___boxed(
    mut v_thm_u2081_3108_: *mut leanh::LeanObject,
    mut v_thm_u2082_3109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3110_: u8 = 0;
    let mut v_r_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3110_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecTheoremNew___lam__0(
        v_thm_u2081_3108_,
        v_thm_u2082_3109_,
    );
    v_r_3111_ = leanh::lean_box((v_res_3110_) as usize);
    return v_r_3111_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(
    mut v_as_3114_: *mut leanh::LeanObject,
    mut v_i_3115_: usize,
    mut v_stop_3116_: usize,
    mut v_b_3117_: *mut leanh::LeanObject,
    mut v___y_3118_: *mut leanh::LeanObject,
    mut v___y_3119_: *mut leanh::LeanObject,
    mut v___y_3120_: *mut leanh::LeanObject,
    mut v___y_3121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3123_: u8 = 0;
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: usize = 0;
    let mut v___x_3128_: usize = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3123_ = lean_usize_dec_eq(v_i_3115_, v_stop_3116_);
                if v___x_3123_ == 0 {
                    v___x_3124_ = lean_array_uget_borrowed(v_as_3114_, v_i_3115_);
                    leanh::lean_inc(v___x_3124_);
                    v___x_3125_ = l_Lean_Meta_mkCongrFun(
                        v_b_3117_,
                        v___x_3124_,
                        v___y_3118_,
                        v___y_3119_,
                        v___y_3120_,
                        v___y_3121_,
                    );
                    if leanh::lean_obj_tag(v___x_3125_) == 0 {
                        v_a_3126_ = leanh::lean_ctor_get(v___x_3125_, 0);
                        leanh::lean_inc(v_a_3126_);
                        leanh::lean_dec_ref_known(v___x_3125_, 1);
                        v___x_3127_ = 1usize;
                        v___x_3128_ = lean_usize_add(v_i_3115_, v___x_3127_);
                        v_i_3115_ = v___x_3128_;
                        v_b_3117_ = v_a_3126_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3125_;
                    }
                } else {
                    v___x_3130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3130_, 0, v_b_3117_);
                    return v___x_3130_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0___boxed(
    mut v_as_3131_: *mut leanh::LeanObject,
    mut v_i_3132_: *mut leanh::LeanObject,
    mut v_stop_3133_: *mut leanh::LeanObject,
    mut v_b_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
    mut v___y_3137_: *mut leanh::LeanObject,
    mut v___y_3138_: *mut leanh::LeanObject,
    mut v___y_3139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3140_: usize = 0;
    let mut v_stop_boxed_3141_: usize = 0;
    let mut v_res_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3140_ = leanh::lean_unbox_usize(v_i_3132_);
    leanh::lean_dec(v_i_3132_);
    v_stop_boxed_3141_ = leanh::lean_unbox_usize(v_stop_3133_);
    leanh::lean_dec(v_stop_3133_);
    v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(v_as_3131_, v_i_boxed_3140_, v_stop_boxed_3141_, v_b_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
    leanh::lean_dec(v___y_3138_);
    leanh::lean_dec_ref(v___y_3137_);
    leanh::lean_dec(v___y_3136_);
    leanh::lean_dec_ref(v___y_3135_);
    leanh::lean_dec_ref(v_as_3131_);
    return v_res_3142_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2() -> u64 {
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3147_: u64 = 0;
    v___x_3146_ = 2;
    v___x_3147_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3146_);
    return v___x_3147_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate(
    mut v_specThm_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
    mut v_a_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_proof_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v_etaArgs_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: u8 = 0;
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: u8 = 0;
    let mut v_arg_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: u8 = 0;
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3181_: u8 = 0;
    let mut v_ctxApprox_3182_: u8 = 0;
    let mut v_quasiPatternApprox_3183_: u8 = 0;
    let mut v_constApprox_3184_: u8 = 0;
    let mut v_isDefEqStuckEx_3185_: u8 = 0;
    let mut v_unificationHints_3186_: u8 = 0;
    let mut v_proofIrrelevance_3187_: u8 = 0;
    let mut v_assignSyntheticOpaque_3188_: u8 = 0;
    let mut v_offsetCnstrs_3189_: u8 = 0;
    let mut v_etaStruct_3190_: u8 = 0;
    let mut v_univApprox_3191_: u8 = 0;
    let mut v_iota_3192_: u8 = 0;
    let mut v_beta_3193_: u8 = 0;
    let mut v_proj_3194_: u8 = 0;
    let mut v_zeta_3195_: u8 = 0;
    let mut v_zetaDelta_3196_: u8 = 0;
    let mut v_zetaUnused_3197_: u8 = 0;
    let mut v_zetaHave_3198_: u8 = 0;
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v_trackZetaDelta_3202_: u8 = 0;
    let mut v_zetaDeltaSet_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3209_: u8 = 0;
    let mut v_inTypeClassResolution_3210_: u8 = 0;
    let mut v_cacheInferType_3211_: u8 = 0;
    let mut v___x_3212_: u8 = 0;
    let mut v_config_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u64 = 0;
    let mut v___x_3216_: u64 = 0;
    let mut v___x_3217_: u64 = 0;
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: u64 = 0;
    let mut v___x_3220_: u64 = 0;
    let mut v_key_3221_: u64 = 0;
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v_fst_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3234_: u8 = 0;
    let mut v_a_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3241_: u8 = 0;
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut v_a_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v___y_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3271_: u8 = 0;
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3275_: u8 = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: u8 = 0;
    let mut v___x_3279_: usize = 0;
    let mut v___x_3280_: usize = 0;
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: usize = 0;
    let mut v___x_3283_: usize = 0;
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3285_: u8 = 0;
    let mut v_unused_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_a_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v_reuseFailAlloc_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_proof_3154_ = leanh::lean_ctor_get(v_specThm_3148_, 1);
                leanh::lean_inc_ref(v_proof_3154_);
                v_kind_3155_ = leanh::lean_ctor_get(v_specThm_3148_, 2);
                leanh::lean_inc_ref(v_kind_3155_);
                leanh::lean_dec_ref(v_specThm_3148_);
                v___x_3156_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_instantiate(
                    v_proof_3154_,
                    v_a_3149_,
                    v_a_3150_,
                    v_a_3151_,
                    v_a_3152_,
                );
                if leanh::lean_obj_tag(v___x_3156_) == 0 {
                    v_a_3157_ = leanh::lean_ctor_get(v___x_3156_, 0);
                    leanh::lean_inc(v_a_3157_);
                    v_snd_3158_ = leanh::lean_ctor_get(v_a_3157_, 1);
                    leanh::lean_inc(v_snd_3158_);
                    v_snd_3159_ = leanh::lean_ctor_get(v_snd_3158_, 1);
                    leanh::lean_inc(v_snd_3159_);
                    if leanh::lean_obj_tag(v_kind_3155_) == 1 {
                        v_fst_3160_ = leanh::lean_ctor_get(v_a_3157_, 0);
                        leanh::lean_inc(v_fst_3160_);
                        leanh::lean_dec(v_a_3157_);
                        v_fst_3161_ = leanh::lean_ctor_get(v_snd_3158_, 0);
                        leanh::lean_inc(v_fst_3161_);
                        leanh::lean_dec(v_snd_3158_);
                        v_fst_3162_ = leanh::lean_ctor_get(v_snd_3159_, 0);
                        v_snd_3163_ = leanh::lean_ctor_get(v_snd_3159_, 1);
                        v_isSharedCheck_3298_ =
                            (!leanh::lean_is_exclusive(v_snd_3159_)) as u8;
                        if v_isSharedCheck_3298_ == 0 {
                            v___x_3165_ = v_snd_3159_;
                            v_isShared_3166_ = v_isSharedCheck_3298_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3163_);
                            leanh::lean_inc(v_fst_3162_);
                            leanh::lean_dec(v_snd_3159_);
                            v___x_3165_ = leanh::lean_box(0);
                            v_isShared_3166_ = v_isSharedCheck_3298_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3159_);
                        leanh::lean_dec(v_snd_3158_);
                        leanh::lean_dec(v_a_3157_);
                        leanh::lean_dec_ref(v_kind_3155_);
                        return v___x_3156_;
                    }
                } else {
                    leanh::lean_dec_ref(v_kind_3155_);
                    return v___x_3156_;
                }
            }
            1 => {
                v_etaArgs_3167_ = leanh::lean_ctor_get(v_kind_3155_, 0);
                leanh::lean_inc(v_etaArgs_3167_);
                leanh::lean_dec_ref_known(v_kind_3155_, 1);
                v___x_3168_ = leanh::lean_unsigned_to_nat(0);
                v___x_3169_ = lean_nat_dec_eq(v_etaArgs_3167_, v___x_3168_);
                if v___x_3169_ == 0 {
                    v___x_3170_ = l_Lean_Expr_cleanupAnnotations(v_snd_3163_);
                    v___x_3171_ = l_Lean_Expr_isApp(v___x_3170_);
                    if v___x_3171_ == 0 {
                        leanh::lean_dec_ref(v___x_3170_);
                        leanh::lean_dec(v_etaArgs_3167_);
                        leanh::lean_del_object(v___x_3165_);
                        leanh::lean_dec(v_fst_3162_);
                        leanh::lean_dec(v_fst_3161_);
                        leanh::lean_dec(v_fst_3160_);
                        return v___x_3156_;
                    } else {
                        v___x_3172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3170_);
                        v___x_3173_ = l_Lean_Expr_isApp(v___x_3172_);
                        if v___x_3173_ == 0 {
                            leanh::lean_dec_ref(v___x_3172_);
                            leanh::lean_dec(v_etaArgs_3167_);
                            leanh::lean_del_object(v___x_3165_);
                            leanh::lean_dec(v_fst_3162_);
                            leanh::lean_dec(v_fst_3161_);
                            leanh::lean_dec(v_fst_3160_);
                            return v___x_3156_;
                        } else {
                            v___x_3174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3172_);
                            v___x_3175_ = l_Lean_Expr_isApp(v___x_3174_);
                            if v___x_3175_ == 0 {
                                leanh::lean_dec_ref(v___x_3174_);
                                leanh::lean_dec(v_etaArgs_3167_);
                                leanh::lean_del_object(v___x_3165_);
                                leanh::lean_dec(v_fst_3162_);
                                leanh::lean_dec(v_fst_3161_);
                                leanh::lean_dec(v_fst_3160_);
                                return v___x_3156_;
                            } else {
                                v_arg_3176_ = leanh::lean_ctor_get(v___x_3174_, 1);
                                leanh::lean_inc_ref(v_arg_3176_);
                                v___x_3177_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3174_);
                                v___x_3178_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1;
                                v___x_3179_ = l_Lean_Expr_isConstOf(v___x_3177_, v___x_3178_);
                                leanh::lean_dec_ref(v___x_3177_);
                                if v___x_3179_ == 0 {
                                    leanh::lean_dec_ref(v_arg_3176_);
                                    leanh::lean_dec(v_etaArgs_3167_);
                                    leanh::lean_del_object(v___x_3165_);
                                    leanh::lean_dec(v_fst_3162_);
                                    leanh::lean_dec(v_fst_3161_);
                                    leanh::lean_dec(v_fst_3160_);
                                    return v___x_3156_;
                                } else {
                                    leanh::lean_dec_ref_known(v___x_3156_, 1);
                                    v___x_3180_ = l_Lean_Meta_Context_config(v_a_3149_);
                                    v_foApprox_3181_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 0 as u32);
                                    v_ctxApprox_3182_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 1 as u32);
                                    v_quasiPatternApprox_3183_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 2 as u32);
                                    v_constApprox_3184_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 3 as u32);
                                    v_isDefEqStuckEx_3185_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 4 as u32);
                                    v_unificationHints_3186_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 5 as u32);
                                    v_proofIrrelevance_3187_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 6 as u32);
                                    v_assignSyntheticOpaque_3188_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 7 as u32);
                                    v_offsetCnstrs_3189_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 8 as u32);
                                    v_etaStruct_3190_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 10 as u32);
                                    v_univApprox_3191_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 11 as u32);
                                    v_iota_3192_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 12 as u32);
                                    v_beta_3193_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 13 as u32);
                                    v_proj_3194_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 14 as u32);
                                    v_zeta_3195_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 15 as u32);
                                    v_zetaDelta_3196_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 16 as u32);
                                    v_zetaUnused_3197_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 17 as u32);
                                    v_zetaHave_3198_ =
                                        leanh::lean_ctor_get_uint8(v___x_3180_, 18 as u32);
                                    v_isSharedCheck_3297_ =
                                        (!leanh::lean_is_exclusive(v___x_3180_)) as u8;
                                    if v_isSharedCheck_3297_ == 0 {
                                        v___x_3200_ = v___x_3180_;
                                        v_isShared_3201_ = v_isSharedCheck_3297_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_3180_);
                                        v___x_3200_ = leanh::lean_box(0);
                                        v_isShared_3201_ = v_isSharedCheck_3297_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_etaArgs_3167_);
                    leanh::lean_del_object(v___x_3165_);
                    leanh::lean_dec(v_snd_3163_);
                    leanh::lean_dec(v_fst_3162_);
                    leanh::lean_dec(v_fst_3161_);
                    leanh::lean_dec(v_fst_3160_);
                    return v___x_3156_;
                }
            }
            2 => {
                v_trackZetaDelta_3202_ = leanh::lean_ctor_get_uint8(
                    v_a_3149_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3203_ = leanh::lean_ctor_get(v_a_3149_, 1);
                v_lctx_3204_ = leanh::lean_ctor_get(v_a_3149_, 2);
                v_localInstances_3205_ = leanh::lean_ctor_get(v_a_3149_, 3);
                v_defEqCtx_x3f_3206_ = leanh::lean_ctor_get(v_a_3149_, 4);
                v_synthPendingDepth_3207_ = leanh::lean_ctor_get(v_a_3149_, 5);
                v_canUnfold_x3f_3208_ = leanh::lean_ctor_get(v_a_3149_, 6);
                v_univApprox_3209_ = leanh::lean_ctor_get_uint8(
                    v_a_3149_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3210_ = leanh::lean_ctor_get_uint8(
                    v_a_3149_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3211_ = leanh::lean_ctor_get_uint8(
                    v_a_3149_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3212_ = 2;
                if v_isShared_3201_ == 0 {
                    v_config_3214_ = v___x_3200_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3296_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        0 as u32,
                        v_foApprox_3181_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        1 as u32,
                        v_ctxApprox_3182_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        2 as u32,
                        v_quasiPatternApprox_3183_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        3 as u32,
                        v_constApprox_3184_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        4 as u32,
                        v_isDefEqStuckEx_3185_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        5 as u32,
                        v_unificationHints_3186_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        6 as u32,
                        v_proofIrrelevance_3187_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        7 as u32,
                        v_assignSyntheticOpaque_3188_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        8 as u32,
                        v_offsetCnstrs_3189_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        10 as u32,
                        v_etaStruct_3190_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        11 as u32,
                        v_univApprox_3191_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        12 as u32,
                        v_iota_3192_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        13 as u32,
                        v_beta_3193_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        14 as u32,
                        v_proj_3194_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        15 as u32,
                        v_zeta_3195_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        16 as u32,
                        v_zetaDelta_3196_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        17 as u32,
                        v_zetaUnused_3197_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3296_,
                        18 as u32,
                        v_zetaHave_3198_,
                    );
                    v_config_3214_ = v_reuseFailAlloc_3296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(v_config_3214_, 9 as u32, v___x_3212_);
                v___x_3215_ = l_Lean_Meta_Context_configKey(v_a_3149_);
                v___x_3216_ = 3u64;
                v___x_3217_ = lean_uint64_shift_right(v___x_3215_, v___x_3216_);
                v___x_3218_ = 0;
                v___x_3219_ = lean_uint64_shift_left(v___x_3217_, v___x_3216_);
                v___x_3220_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__2,
                );
                v_key_3221_ = lean_uint64_lor(v___x_3219_, v___x_3220_);
                v___x_3222_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3222_, 0, v_config_3214_);
                leanh::lean_ctor_set_uint64(
                    v___x_3222_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_3221_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3208_);
                leanh::lean_inc(v_synthPendingDepth_3207_);
                leanh::lean_inc(v_defEqCtx_x3f_3206_);
                leanh::lean_inc_ref(v_localInstances_3205_);
                leanh::lean_inc_ref(v_lctx_3204_);
                leanh::lean_inc(v_zetaDeltaSet_3203_);
                v___x_3223_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3223_, 0, v___x_3222_);
                leanh::lean_ctor_set(v___x_3223_, 1, v_zetaDeltaSet_3203_);
                leanh::lean_ctor_set(v___x_3223_, 2, v_lctx_3204_);
                leanh::lean_ctor_set(v___x_3223_, 3, v_localInstances_3205_);
                leanh::lean_ctor_set(v___x_3223_, 4, v_defEqCtx_x3f_3206_);
                leanh::lean_ctor_set(v___x_3223_, 5, v_synthPendingDepth_3207_);
                leanh::lean_ctor_set(v___x_3223_, 6, v_canUnfold_x3f_3208_);
                leanh::lean_ctor_set_uint8(
                    v___x_3223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3202_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3209_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3210_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3223_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3211_,
                );
                v___x_3224_ = l_Lean_Meta_forallMetaBoundedTelescope(
                    v_arg_3176_,
                    v_etaArgs_3167_,
                    v___x_3218_,
                    v___x_3223_,
                    v_a_3150_,
                    v_a_3151_,
                    v_a_3152_,
                );
                leanh::lean_dec_ref_known(v___x_3223_, 7);
                if leanh::lean_obj_tag(v___x_3224_) == 0 {
                    v_a_3225_ = leanh::lean_ctor_get(v___x_3224_, 0);
                    leanh::lean_inc(v_a_3225_);
                    leanh::lean_dec_ref_known(v___x_3224_, 1);
                    v_snd_3226_ = leanh::lean_ctor_get(v_a_3225_, 1);
                    v_fst_3227_ = leanh::lean_ctor_get(v_a_3225_, 0);
                    v_isSharedCheck_3287_ = (!leanh::lean_is_exclusive(v_a_3225_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3229_ = v_a_3225_;
                        v_isShared_3230_ = v_isSharedCheck_3287_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3226_);
                        leanh::lean_inc(v_fst_3227_);
                        leanh::lean_dec(v_a_3225_);
                        v___x_3229_ = leanh::lean_box(0);
                        v_isShared_3230_ = v_isSharedCheck_3287_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3165_);
                    leanh::lean_dec(v_fst_3162_);
                    leanh::lean_dec(v_fst_3161_);
                    leanh::lean_dec(v_fst_3160_);
                    v_a_3288_ = leanh::lean_ctor_get(v___x_3224_, 0);
                    v_isSharedCheck_3295_ = (!leanh::lean_is_exclusive(v___x_3224_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3290_ = v___x_3224_;
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3288_);
                        leanh::lean_dec(v___x_3224_);
                        v___x_3290_ = leanh::lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 17;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_3231_ = leanh::lean_ctor_get(v_snd_3226_, 0);
                v_isSharedCheck_3285_ = (!leanh::lean_is_exclusive(v_snd_3226_)) as u8;
                if v_isSharedCheck_3285_ == 0 {
                    v_unused_3286_ = leanh::lean_ctor_get(v_snd_3226_, 1);
                    leanh::lean_dec(v_unused_3286_);
                    v___x_3233_ = v_snd_3226_;
                    v_isShared_3234_ = v_isSharedCheck_3285_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_3231_);
                    leanh::lean_dec(v_snd_3226_);
                    v___x_3233_ = leanh::lean_box(0);
                    v_isShared_3234_ = v_isSharedCheck_3285_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3276_ = lean_array_get_size(v_fst_3227_);
                v___x_3277_ = lean_nat_dec_lt(v___x_3168_, v___x_3276_);
                if v___x_3277_ == 0 {
                    v_a_3236_ = v_fst_3162_;
                    state = 6;
                    continue;
                } else {
                    v___x_3278_ = lean_nat_dec_le(v___x_3276_, v___x_3276_);
                    if v___x_3278_ == 0 {
                        if v___x_3277_ == 0 {
                            v_a_3236_ = v_fst_3162_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3279_ = 0usize;
                            v___x_3280_ = lean_usize_of_nat(v___x_3276_);
                            v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(v_fst_3227_, v___x_3279_, v___x_3280_, v_fst_3162_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
                            v___y_3266_ = v___x_3281_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_3282_ = 0usize;
                        v___x_3283_ = lean_usize_of_nat(v___x_3276_);
                        v___x_3284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate_spec__0(v_fst_3227_, v___x_3282_, v___x_3283_, v_fst_3162_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
                        v___y_3266_ = v___x_3284_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                leanh::lean_inc(v_a_3152_);
                leanh::lean_inc_ref(v_a_3151_);
                leanh::lean_inc(v_a_3150_);
                leanh::lean_inc_ref(v_a_3149_);
                leanh::lean_inc_ref(v_a_3236_);
                v___x_3237_ =
                    lean_infer_type(v_a_3236_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
                if leanh::lean_obj_tag(v___x_3237_) == 0 {
                    v_a_3238_ = leanh::lean_ctor_get(v___x_3237_, 0);
                    v_isSharedCheck_3256_ = (!leanh::lean_is_exclusive(v___x_3237_)) as u8;
                    if v_isSharedCheck_3256_ == 0 {
                        v___x_3240_ = v___x_3237_;
                        v_isShared_3241_ = v_isSharedCheck_3256_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3238_);
                        leanh::lean_dec(v___x_3237_);
                        v___x_3240_ = leanh::lean_box(0);
                        v_isShared_3241_ = v_isSharedCheck_3256_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_3236_);
                    leanh::lean_del_object(v___x_3233_);
                    leanh::lean_dec(v_fst_3231_);
                    leanh::lean_del_object(v___x_3229_);
                    leanh::lean_dec(v_fst_3227_);
                    leanh::lean_del_object(v___x_3165_);
                    leanh::lean_dec(v_fst_3161_);
                    leanh::lean_dec(v_fst_3160_);
                    v_a_3257_ = leanh::lean_ctor_get(v___x_3237_, 0);
                    v_isSharedCheck_3264_ = (!leanh::lean_is_exclusive(v___x_3237_)) as u8;
                    if v_isSharedCheck_3264_ == 0 {
                        v___x_3259_ = v___x_3237_;
                        v_isShared_3260_ = v_isSharedCheck_3264_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3257_);
                        leanh::lean_dec(v___x_3237_);
                        v___x_3259_ = leanh::lean_box(0);
                        v_isShared_3260_ = v_isSharedCheck_3264_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3242_ = l_Array_append___redArg(v_fst_3160_, v_fst_3227_);
                leanh::lean_dec(v_fst_3227_);
                v___x_3243_ = l_Array_append___redArg(v_fst_3161_, v_fst_3231_);
                leanh::lean_dec(v_fst_3231_);
                if v_isShared_3234_ == 0 {
                    leanh::lean_ctor_set(v___x_3233_, 1, v_a_3238_);
                    leanh::lean_ctor_set(v___x_3233_, 0, v_a_3236_);
                    v___x_3245_ = v___x_3233_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 1, v_a_3238_);
                    v___x_3245_ = v_reuseFailAlloc_3255_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3230_ == 0 {
                    leanh::lean_ctor_set(v___x_3229_, 1, v___x_3245_);
                    leanh::lean_ctor_set(v___x_3229_, 0, v___x_3243_);
                    v___x_3247_ = v___x_3229_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3243_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3245_);
                    v___x_3247_ = v_reuseFailAlloc_3254_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3166_ == 0 {
                    leanh::lean_ctor_set(v___x_3165_, 1, v___x_3247_);
                    leanh::lean_ctor_set(v___x_3165_, 0, v___x_3242_);
                    v___x_3249_ = v___x_3165_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3253_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3242_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3247_);
                    v___x_3249_ = v_reuseFailAlloc_3253_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3241_ == 0 {
                    leanh::lean_ctor_set(v___x_3240_, 0, v___x_3249_);
                    v___x_3251_ = v___x_3240_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3249_);
                    v___x_3251_ = v_reuseFailAlloc_3252_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3251_;
            }
            12 => {
                if v_isShared_3260_ == 0 {
                    v___x_3262_ = v___x_3259_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
                    v___x_3262_ = v_reuseFailAlloc_3263_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3262_;
            }
            14 => {
                if leanh::lean_obj_tag(v___y_3266_) == 0 {
                    v_a_3267_ = leanh::lean_ctor_get(v___y_3266_, 0);
                    leanh::lean_inc(v_a_3267_);
                    leanh::lean_dec_ref_known(v___y_3266_, 1);
                    v_a_3236_ = v_a_3267_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_3233_);
                    leanh::lean_dec(v_fst_3231_);
                    leanh::lean_del_object(v___x_3229_);
                    leanh::lean_dec(v_fst_3227_);
                    leanh::lean_del_object(v___x_3165_);
                    leanh::lean_dec(v_fst_3161_);
                    leanh::lean_dec(v_fst_3160_);
                    v_a_3268_ = leanh::lean_ctor_get(v___y_3266_, 0);
                    v_isSharedCheck_3275_ = (!leanh::lean_is_exclusive(v___y_3266_)) as u8;
                    if v_isSharedCheck_3275_ == 0 {
                        v___x_3270_ = v___y_3266_;
                        v_isShared_3271_ = v_isSharedCheck_3275_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3268_);
                        leanh::lean_dec(v___y_3266_);
                        v___x_3270_ = leanh::lean_box(0);
                        v_isShared_3271_ = v_isSharedCheck_3275_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_3271_ == 0 {
                    v___x_3273_ = v___x_3270_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3274_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
                    v___x_3273_ = v_reuseFailAlloc_3274_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3273_;
            }
            17 => {
                if v_isShared_3291_ == 0 {
                    v___x_3293_ = v___x_3290_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3294_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
                    v___x_3293_ = v_reuseFailAlloc_3294_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___boxed(
    mut v_specThm_3299_: *mut leanh::LeanObject,
    mut v_a_3300_: *mut leanh::LeanObject,
    mut v_a_3301_: *mut leanh::LeanObject,
    mut v_a_3302_: *mut leanh::LeanObject,
    mut v_a_3303_: *mut leanh::LeanObject,
    mut v_a_3304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3305_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate(
        v_specThm_3299_,
        v_a_3300_,
        v_a_3301_,
        v_a_3302_,
        v_a_3303_,
    );
    leanh::lean_dec(v_a_3303_);
    leanh::lean_dec_ref(v_a_3302_);
    leanh::lean_dec(v_a_3301_);
    leanh::lean_dec_ref(v_a_3300_);
    return v_res_3305_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3306_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3306_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__0);
    v___x_3308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3308_, 0, v___x_3307_);
    return v___x_3308_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0(
    mut v_00_u03b2_3309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0___closed__1);
    return v___x_3310_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3311_ = l_Lean_Meta_DiscrTree_empty(leanh::lean_box(0));
    return v___x_3311_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3312_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default_spec__0(leanh::lean_box(0));
    return v___x_3312_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__1,
    );
    v___x_3314_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0,
    );
    v___x_3315_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3315_, 0, v___x_3314_);
    leanh::lean_ctor_set(v___x_3315_, 1, v___x_3313_);
    return v___x_3315_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default()
-> *mut leanh::LeanObject {
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3316_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__2,
    );
    return v___x_3316_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew()
-> *mut leanh::LeanObject {
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3317_ = l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default;
    return v___x_3317_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(
    mut v_msgData_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
    mut v___y_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = lean_st_ref_get(v___y_3322_);
    v_env_3325_ = leanh::lean_ctor_get(v___x_3324_, 0);
    leanh::lean_inc_ref(v_env_3325_);
    leanh::lean_dec(v___x_3324_);
    v___x_3326_ = lean_st_ref_get(v___y_3320_);
    v_mctx_3327_ = leanh::lean_ctor_get(v___x_3326_, 0);
    leanh::lean_inc_ref(v_mctx_3327_);
    leanh::lean_dec(v___x_3326_);
    v_lctx_3328_ = leanh::lean_ctor_get(v___y_3319_, 2);
    v_options_3329_ = leanh::lean_ctor_get(v___y_3321_, 2);
    leanh::lean_inc_ref(v_options_3329_);
    leanh::lean_inc_ref(v_lctx_3328_);
    v___x_3330_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3330_, 0, v_env_3325_);
    leanh::lean_ctor_set(v___x_3330_, 1, v_mctx_3327_);
    leanh::lean_ctor_set(v___x_3330_, 2, v_lctx_3328_);
    leanh::lean_ctor_set(v___x_3330_, 3, v_options_3329_);
    v___x_3331_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3331_, 0, v___x_3330_);
    leanh::lean_ctor_set(v___x_3331_, 1, v_msgData_3318_);
    v___x_3332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3332_, 0, v___x_3331_);
    return v___x_3332_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0___boxed(
    mut v_msgData_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
    mut v___y_3335_: *mut leanh::LeanObject,
    mut v___y_3336_: *mut leanh::LeanObject,
    mut v___y_3337_: *mut leanh::LeanObject,
    mut v___y_3338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3339_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msgData_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
    leanh::lean_dec(v___y_3337_);
    leanh::lean_dec_ref(v___y_3336_);
    leanh::lean_dec(v___y_3335_);
    leanh::lean_dec_ref(v___y_3334_);
    return v_res_3339_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(
    mut v_msg_3340_: *mut leanh::LeanObject,
    mut v___y_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3356_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3346_ = leanh::lean_ctor_get(v___y_3343_, 5);
                v___x_3347_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
                v_a_3348_ = leanh::lean_ctor_get(v___x_3347_, 0);
                v_isSharedCheck_3356_ = (!leanh::lean_is_exclusive(v___x_3347_)) as u8;
                if v_isSharedCheck_3356_ == 0 {
                    v___x_3350_ = v___x_3347_;
                    v_isShared_3351_ = v_isSharedCheck_3356_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3348_);
                    leanh::lean_dec(v___x_3347_);
                    v___x_3350_ = leanh::lean_box(0);
                    v_isShared_3351_ = v_isSharedCheck_3356_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3346_);
                v___x_3352_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3352_, 0, v_ref_3346_);
                leanh::lean_ctor_set(v___x_3352_, 1, v_a_3348_);
                if v_isShared_3351_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3350_, 1);
                    leanh::lean_ctor_set(v___x_3350_, 0, v___x_3352_);
                    v___x_3354_ = v___x_3350_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
                    v___x_3354_ = v_reuseFailAlloc_3355_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg___boxed(
    mut v_msg_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3363_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v_msg_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
    leanh::lean_dec(v___y_3361_);
    leanh::lean_dec_ref(v___y_3360_);
    leanh::lean_dec(v___y_3359_);
    leanh::lean_dec_ref(v___y_3358_);
    return v_res_3363_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3365_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__0;
    v___x_3366_ = l_Lean_stringToMessageData(v___x_3365_);
    return v___x_3366_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0(
    mut v_type_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u8 = 0;
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: u8 = 0;
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: u8 = 0;
    let mut v_arg_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: u8 = 0;
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: u8 = 0;
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_3374_);
                v___x_3385_ = l_Lean_Expr_cleanupAnnotations(v_type_3374_);
                v___x_3386_ = l_Lean_Expr_isApp(v___x_3385_);
                if v___x_3386_ == 0 {
                    leanh::lean_dec_ref(v___x_3385_);
                    state = 1;
                    continue;
                } else {
                    v___x_3387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3385_);
                    v___x_3388_ = l_Lean_Expr_isApp(v___x_3387_);
                    if v___x_3388_ == 0 {
                        leanh::lean_dec_ref(v___x_3387_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3387_);
                        v___x_3390_ = l_Lean_Expr_isApp(v___x_3389_);
                        if v___x_3390_ == 0 {
                            leanh::lean_dec_ref(v___x_3389_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_3391_ = leanh::lean_ctor_get(v___x_3389_, 1);
                            leanh::lean_inc_ref(v_arg_3391_);
                            v___x_3392_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3389_);
                            v___x_3393_ = l_Lean_Expr_isApp(v___x_3392_);
                            if v___x_3393_ == 0 {
                                leanh::lean_dec_ref(v___x_3392_);
                                leanh::lean_dec_ref(v_arg_3391_);
                                state = 1;
                                continue;
                            } else {
                                v___x_3394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3392_);
                                v___x_3395_ = l_Lean_Expr_isApp(v___x_3394_);
                                if v___x_3395_ == 0 {
                                    leanh::lean_dec_ref(v___x_3394_);
                                    leanh::lean_dec_ref(v_arg_3391_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3394_);
                                    v___x_3397_ = l_Lean_Expr_isApp(v___x_3396_);
                                    if v___x_3397_ == 0 {
                                        leanh::lean_dec_ref(v___x_3396_);
                                        leanh::lean_dec_ref(v_arg_3391_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3398_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3396_);
                                        v___x_3399_ = l_Lean_Expr_isApp(v___x_3398_);
                                        if v___x_3399_ == 0 {
                                            leanh::lean_dec_ref(v___x_3398_);
                                            leanh::lean_dec_ref(v_arg_3391_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_3400_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3398_);
                                            v___x_3401_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5;
                                            v___x_3402_ =
                                                l_Lean_Expr_isConstOf(v___x_3400_, v___x_3401_);
                                            leanh::lean_dec_ref(v___x_3400_);
                                            if v___x_3402_ == 0 {
                                                leanh::lean_dec_ref(v_arg_3391_);
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_dec_ref(v_type_3374_);
                                                v___x_3403_ = leanh::lean_box(0);
                                                v___x_3404_ =
                                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3404_,
                                                    0,
                                                    v_arg_3391_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3404_,
                                                    1,
                                                    v___x_3403_,
                                                );
                                                v___x_3405_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3405_,
                                                    0,
                                                    v___x_3404_,
                                                );
                                                return v___x_3405_;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3381_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__1);
                v___x_3382_ = l_Lean_indentExpr(v_type_3374_);
                v___x_3383_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3383_, 0, v___x_3381_);
                leanh::lean_ctor_set(v___x_3383_, 1, v___x_3382_);
                v___x_3384_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v___x_3383_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_);
                return v___x_3384_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___boxed(
    mut v_type_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3412_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0(
        v_type_3406_,
        v___y_3407_,
        v___y_3408_,
        v___y_3409_,
        v___y_3410_,
    );
    leanh::lean_dec(v___y_3410_);
    leanh::lean_dec_ref(v___y_3409_);
    leanh::lean_dec(v___y_3408_);
    leanh::lean_dec_ref(v___y_3407_);
    return v_res_3412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(
    mut v_expr_3416_: *mut leanh::LeanObject,
    mut v_levelParams_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_a_3420_: *mut leanh::LeanObject,
    mut v_a_3421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v_fst_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3438_: u8 = 0;
    let mut v_a_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v_a_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3450_: u8 = 0;
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3423_ =
                    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessExprPattern(
                        v_expr_3416_,
                        v_levelParams_3417_,
                        v_a_3418_,
                        v_a_3419_,
                        v_a_3420_,
                        v_a_3421_,
                    );
                if leanh::lean_obj_tag(v___x_3423_) == 0 {
                    v_a_3424_ = leanh::lean_ctor_get(v___x_3423_, 0);
                    leanh::lean_inc(v_a_3424_);
                    leanh::lean_dec_ref_known(v___x_3423_, 1);
                    v_fst_3425_ = leanh::lean_ctor_get(v_a_3424_, 0);
                    leanh::lean_inc(v_fst_3425_);
                    v_snd_3426_ = leanh::lean_ctor_get(v_a_3424_, 1);
                    leanh::lean_inc_n(v_snd_3426_, 2);
                    leanh::lean_dec(v_a_3424_);
                    v___f_3427_ =
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__0;
                    v___x_3428_ =
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1;
                    v___x_3429_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(leanh::lean_box(0), v_fst_3425_, v_snd_3426_, v___f_3427_, v_snd_3426_, v___x_3428_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
                    if leanh::lean_obj_tag(v___x_3429_) == 0 {
                        v_a_3430_ = leanh::lean_ctor_get(v___x_3429_, 0);
                        v_isSharedCheck_3438_ =
                            (!leanh::lean_is_exclusive(v___x_3429_)) as u8;
                        if v_isSharedCheck_3438_ == 0 {
                            v___x_3432_ = v___x_3429_;
                            v_isShared_3433_ = v_isSharedCheck_3438_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3430_);
                            leanh::lean_dec(v___x_3429_);
                            v___x_3432_ = leanh::lean_box(0);
                            v_isShared_3433_ = v_isSharedCheck_3438_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3439_ = leanh::lean_ctor_get(v___x_3429_, 0);
                        v_isSharedCheck_3446_ =
                            (!leanh::lean_is_exclusive(v___x_3429_)) as u8;
                        if v_isSharedCheck_3446_ == 0 {
                            v___x_3441_ = v___x_3429_;
                            v_isShared_3442_ = v_isSharedCheck_3446_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3439_);
                            leanh::lean_dec(v___x_3429_);
                            v___x_3441_ = leanh::lean_box(0);
                            v_isShared_3442_ = v_isSharedCheck_3446_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_3447_ = leanh::lean_ctor_get(v___x_3423_, 0);
                    v_isSharedCheck_3454_ = (!leanh::lean_is_exclusive(v___x_3423_)) as u8;
                    if v_isSharedCheck_3454_ == 0 {
                        v___x_3449_ = v___x_3423_;
                        v_isShared_3450_ = v_isSharedCheck_3454_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3447_);
                        leanh::lean_dec(v___x_3423_);
                        v___x_3449_ = leanh::lean_box(0);
                        v_isShared_3450_ = v_isSharedCheck_3454_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3434_ = leanh::lean_ctor_get(v_a_3430_, 0);
                leanh::lean_inc(v_fst_3434_);
                leanh::lean_dec(v_a_3430_);
                if v_isShared_3433_ == 0 {
                    leanh::lean_ctor_set(v___x_3432_, 0, v_fst_3434_);
                    v___x_3436_ = v___x_3432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_fst_3434_);
                    v___x_3436_ = v_reuseFailAlloc_3437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3436_;
            }
            3 => {
                if v_isShared_3442_ == 0 {
                    v___x_3444_ = v___x_3441_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3444_;
            }
            5 => {
                if v_isShared_3450_ == 0 {
                    v___x_3452_ = v___x_3449_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
                    v___x_3452_ = v_reuseFailAlloc_3453_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___boxed(
    mut v_expr_3455_: *mut leanh::LeanObject,
    mut v_levelParams_3456_: *mut leanh::LeanObject,
    mut v_a_3457_: *mut leanh::LeanObject,
    mut v_a_3458_: *mut leanh::LeanObject,
    mut v_a_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(
        v_expr_3455_,
        v_levelParams_3456_,
        v_a_3457_,
        v_a_3458_,
        v_a_3459_,
        v_a_3460_,
    );
    leanh::lean_dec(v_a_3460_);
    leanh::lean_dec_ref(v_a_3459_);
    leanh::lean_dec(v_a_3458_);
    leanh::lean_dec_ref(v_a_3457_);
    return v_res_3462_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr(
    mut v_expr_3463_: *mut leanh::LeanObject,
    mut v_levelParams_3464_: *mut leanh::LeanObject,
    mut v_a_3465_: *mut leanh::LeanObject,
    mut v_a_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
    mut v_a_3468_: *mut leanh::LeanObject,
    mut v_a_3469_: *mut leanh::LeanObject,
    mut v_a_3470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(
        v_expr_3463_,
        v_levelParams_3464_,
        v_a_3467_,
        v_a_3468_,
        v_a_3469_,
        v_a_3470_,
    );
    return v___x_3472_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___boxed(
    mut v_expr_3473_: *mut leanh::LeanObject,
    mut v_levelParams_3474_: *mut leanh::LeanObject,
    mut v_a_3475_: *mut leanh::LeanObject,
    mut v_a_3476_: *mut leanh::LeanObject,
    mut v_a_3477_: *mut leanh::LeanObject,
    mut v_a_3478_: *mut leanh::LeanObject,
    mut v_a_3479_: *mut leanh::LeanObject,
    mut v_a_3480_: *mut leanh::LeanObject,
    mut v_a_3481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr(
        v_expr_3473_,
        v_levelParams_3474_,
        v_a_3475_,
        v_a_3476_,
        v_a_3477_,
        v_a_3478_,
        v_a_3479_,
        v_a_3480_,
    );
    leanh::lean_dec(v_a_3480_);
    leanh::lean_dec_ref(v_a_3479_);
    leanh::lean_dec(v_a_3478_);
    leanh::lean_dec_ref(v_a_3477_);
    leanh::lean_dec(v_a_3476_);
    leanh::lean_dec_ref(v_a_3475_);
    return v_res_3482_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0(
    mut v_00_u03b1_3483_: *mut leanh::LeanObject,
    mut v_msg_3484_: *mut leanh::LeanObject,
    mut v___y_3485_: *mut leanh::LeanObject,
    mut v___y_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
    mut v___y_3488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3490_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v_msg_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
    return v___x_3490_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___boxed(
    mut v_00_u03b1_3491_: *mut leanh::LeanObject,
    mut v_msg_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
    mut v___y_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
    mut v___y_3497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0(
            v_00_u03b1_3491_,
            v_msg_3492_,
            v___y_3493_,
            v___y_3494_,
            v___y_3495_,
            v___y_3496_,
        );
    leanh::lean_dec(v___y_3496_);
    leanh::lean_dec_ref(v___y_3495_);
    leanh::lean_dec(v___y_3494_);
    leanh::lean_dec_ref(v___y_3493_);
    return v_res_3498_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(
    mut v_e_3499_: *mut leanh::LeanObject,
    mut v___y_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3502_: u8 = 0;
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3516_: u8 = 0;
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_unused_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3502_ = l_Lean_Expr_hasMVar(v_e_3499_);
                if v___x_3502_ == 0 {
                    v___x_3503_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3503_, 0, v_e_3499_);
                    return v___x_3503_;
                } else {
                    v___x_3504_ = lean_st_ref_get(v___y_3500_);
                    v_mctx_3505_ = leanh::lean_ctor_get(v___x_3504_, 0);
                    leanh::lean_inc_ref(v_mctx_3505_);
                    leanh::lean_dec(v___x_3504_);
                    v___x_3506_ = l_Lean_instantiateMVarsCore(v_mctx_3505_, v_e_3499_);
                    v_fst_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
                    leanh::lean_inc(v_fst_3507_);
                    v_snd_3508_ = leanh::lean_ctor_get(v___x_3506_, 1);
                    leanh::lean_inc(v_snd_3508_);
                    leanh::lean_dec_ref(v___x_3506_);
                    v___x_3509_ = lean_st_ref_take(v___y_3500_);
                    v_cache_3510_ = leanh::lean_ctor_get(v___x_3509_, 1);
                    v_zetaDeltaFVarIds_3511_ = leanh::lean_ctor_get(v___x_3509_, 2);
                    v_postponed_3512_ = leanh::lean_ctor_get(v___x_3509_, 3);
                    v_diag_3513_ = leanh::lean_ctor_get(v___x_3509_, 4);
                    v_isSharedCheck_3522_ = (!leanh::lean_is_exclusive(v___x_3509_)) as u8;
                    if v_isSharedCheck_3522_ == 0 {
                        v_unused_3523_ = leanh::lean_ctor_get(v___x_3509_, 0);
                        leanh::lean_dec(v_unused_3523_);
                        v___x_3515_ = v___x_3509_;
                        v_isShared_3516_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_3513_);
                        leanh::lean_inc(v_postponed_3512_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_3511_);
                        leanh::lean_inc(v_cache_3510_);
                        leanh::lean_dec(v___x_3509_);
                        v___x_3515_ = leanh::lean_box(0);
                        v_isShared_3516_ = v_isSharedCheck_3522_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3516_ == 0 {
                    leanh::lean_ctor_set(v___x_3515_, 0, v_snd_3508_);
                    v___x_3518_ = v___x_3515_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3521_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v_snd_3508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 1, v_cache_3510_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3521_,
                        2,
                        v_zetaDeltaFVarIds_3511_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 3, v_postponed_3512_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 4, v_diag_3513_);
                    v___x_3518_ = v_reuseFailAlloc_3521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3519_ = lean_st_ref_set(v___y_3500_, v___x_3518_);
                v___x_3520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3520_, 0, v_fst_3507_);
                return v___x_3520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg___boxed(
    mut v_e_3524_: *mut leanh::LeanObject,
    mut v___y_3525_: *mut leanh::LeanObject,
    mut v___y_3526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_3524_, v___y_3525_);
    leanh::lean_dec(v___y_3525_);
    return v_res_3527_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0(
    mut v_e_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
    mut v___y_3531_: *mut leanh::LeanObject,
    mut v___y_3532_: *mut leanh::LeanObject,
    mut v___y_3533_: *mut leanh::LeanObject,
    mut v___y_3534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3536_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_3528_, v___y_3532_);
    return v___x_3536_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___boxed(
    mut v_e_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
    mut v___y_3539_: *mut leanh::LeanObject,
    mut v___y_3540_: *mut leanh::LeanObject,
    mut v___y_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3545_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0(
            v_e_3537_,
            v___y_3538_,
            v___y_3539_,
            v___y_3540_,
            v___y_3541_,
            v___y_3542_,
            v___y_3543_,
        );
    leanh::lean_dec(v___y_3543_);
    leanh::lean_dec_ref(v___y_3542_);
    leanh::lean_dec(v___y_3541_);
    leanh::lean_dec_ref(v___y_3540_);
    leanh::lean_dec(v___y_3539_);
    leanh::lean_dec_ref(v___y_3538_);
    return v_res_3545_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0(
    mut v_k_3546_: *mut leanh::LeanObject,
    mut v___y_3547_: *mut leanh::LeanObject,
    mut v___y_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
    mut v___y_3552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3548_);
    leanh::lean_inc_ref(v___y_3547_);
    v___x_3554_ = leanh::lean_apply_7(
        v_k_3546_,
        v___y_3547_,
        v___y_3548_,
        v___y_3549_,
        v___y_3550_,
        v___y_3551_,
        v___y_3552_,
        leanh::lean_box(0),
    );
    return v___x_3554_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0___boxed(
    mut v_k_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
    mut v___y_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3563_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0(v_k_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
    leanh::lean_dec(v___y_3557_);
    leanh::lean_dec_ref(v___y_3556_);
    return v_res_3563_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(
    mut v_k_3564_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3565_: u8,
    mut v___y_3566_: *mut leanh::LeanObject,
    mut v___y_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
    mut v___y_3571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3578_: u8 = 0;
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3567_);
                leanh::lean_inc_ref(v___y_3566_);
                v___f_3573_ = leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___f_3573_, 0, v_k_3564_);
                leanh::lean_closure_set(v___f_3573_, 1, v___y_3566_);
                leanh::lean_closure_set(v___f_3573_, 2, v___y_3567_);
                v___x_3574_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_3565_,
                    v___f_3573_,
                    v___y_3568_,
                    v___y_3569_,
                    v___y_3570_,
                    v___y_3571_,
                );
                if leanh::lean_obj_tag(v___x_3574_) == 0 {
                    return v___x_3574_;
                } else {
                    v_a_3575_ = leanh::lean_ctor_get(v___x_3574_, 0);
                    v_isSharedCheck_3582_ = (!leanh::lean_is_exclusive(v___x_3574_)) as u8;
                    if v_isSharedCheck_3582_ == 0 {
                        v___x_3577_ = v___x_3574_;
                        v_isShared_3578_ = v_isSharedCheck_3582_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3575_);
                        leanh::lean_dec(v___x_3574_);
                        v___x_3577_ = leanh::lean_box(0);
                        v_isShared_3578_ = v_isSharedCheck_3582_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3578_ == 0 {
                    v___x_3580_ = v___x_3577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3581_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
                    v___x_3580_ = v_reuseFailAlloc_3581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg___boxed(
    mut v_k_3583_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
    mut v___y_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_3592_: u8 = 0;
    let mut v_res_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3592_ =
        (leanh::lean_unbox(v_allowLevelAssignments_3584_) as u8);
    v_res_3593_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(v_k_3583_, v_allowLevelAssignments_boxed_3592_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
    leanh::lean_dec(v___y_3590_);
    leanh::lean_dec_ref(v___y_3589_);
    leanh::lean_dec(v___y_3588_);
    leanh::lean_dec_ref(v___y_3587_);
    leanh::lean_dec(v___y_3586_);
    leanh::lean_dec_ref(v___y_3585_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2(
    mut v_00_u03b1_3594_: *mut leanh::LeanObject,
    mut v_k_3595_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3596_: u8,
    mut v___y_3597_: *mut leanh::LeanObject,
    mut v___y_3598_: *mut leanh::LeanObject,
    mut v___y_3599_: *mut leanh::LeanObject,
    mut v___y_3600_: *mut leanh::LeanObject,
    mut v___y_3601_: *mut leanh::LeanObject,
    mut v___y_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3604_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(v_k_3595_, v_allowLevelAssignments_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
    return v___x_3604_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___boxed(
    mut v_00_u03b1_3605_: *mut leanh::LeanObject,
    mut v_k_3606_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_3607_: *mut leanh::LeanObject,
    mut v___y_3608_: *mut leanh::LeanObject,
    mut v___y_3609_: *mut leanh::LeanObject,
    mut v___y_3610_: *mut leanh::LeanObject,
    mut v___y_3611_: *mut leanh::LeanObject,
    mut v___y_3612_: *mut leanh::LeanObject,
    mut v___y_3613_: *mut leanh::LeanObject,
    mut v___y_3614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_3615_: u8 = 0;
    let mut v_res_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_3615_ =
        (leanh::lean_unbox(v_allowLevelAssignments_3607_) as u8);
    v_res_3616_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2(
            v_00_u03b1_3605_,
            v_k_3606_,
            v_allowLevelAssignments_boxed_3615_,
            v___y_3608_,
            v___y_3609_,
            v___y_3610_,
            v___y_3611_,
            v___y_3612_,
            v___y_3613_,
        );
    leanh::lean_dec(v___y_3613_);
    leanh::lean_dec_ref(v___y_3612_);
    leanh::lean_dec(v___y_3611_);
    leanh::lean_dec_ref(v___y_3610_);
    leanh::lean_dec(v___y_3609_);
    leanh::lean_dec_ref(v___y_3608_);
    return v_res_3616_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(
    mut v_msg_3617_: *mut leanh::LeanObject,
    mut v___y_3618_: *mut leanh::LeanObject,
    mut v___y_3619_: *mut leanh::LeanObject,
    mut v___y_3620_: *mut leanh::LeanObject,
    mut v___y_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3628_: u8 = 0;
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3623_ = leanh::lean_ctor_get(v___y_3620_, 5);
                v___x_3624_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_);
                v_a_3625_ = leanh::lean_ctor_get(v___x_3624_, 0);
                v_isSharedCheck_3633_ = (!leanh::lean_is_exclusive(v___x_3624_)) as u8;
                if v_isSharedCheck_3633_ == 0 {
                    v___x_3627_ = v___x_3624_;
                    v_isShared_3628_ = v_isSharedCheck_3633_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3625_);
                    leanh::lean_dec(v___x_3624_);
                    v___x_3627_ = leanh::lean_box(0);
                    v_isShared_3628_ = v_isSharedCheck_3633_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3623_);
                v___x_3629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3629_, 0, v_ref_3623_);
                leanh::lean_ctor_set(v___x_3629_, 1, v_a_3625_);
                if v_isShared_3628_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3627_, 1);
                    leanh::lean_ctor_set(v___x_3627_, 0, v___x_3629_);
                    v___x_3631_ = v___x_3627_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
                    v___x_3631_ = v_reuseFailAlloc_3632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg___boxed(
    mut v_msg_3634_: *mut leanh::LeanObject,
    mut v___y_3635_: *mut leanh::LeanObject,
    mut v___y_3636_: *mut leanh::LeanObject,
    mut v___y_3637_: *mut leanh::LeanObject,
    mut v___y_3638_: *mut leanh::LeanObject,
    mut v___y_3639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3640_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(
            v_msg_3634_,
            v___y_3635_,
            v___y_3636_,
            v___y_3637_,
            v___y_3638_,
        );
    leanh::lean_dec(v___y_3638_);
    leanh::lean_dec_ref(v___y_3637_);
    leanh::lean_dec(v___y_3636_);
    leanh::lean_dec_ref(v___y_3635_);
    return v_res_3640_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3642_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__0;
    v___x_3643_ = l_Lean_stringToMessageData(v___x_3642_);
    return v___x_3643_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v___x_3647_: u8,
    mut v___x_3648_: *mut leanh::LeanObject,
    mut v___x_3649_: *mut leanh::LeanObject,
    mut v___x_3650_: *mut leanh::LeanObject,
    mut v_a_3651_: *mut leanh::LeanObject,
    mut v_proof_3652_: *mut leanh::LeanObject,
    mut v_prio_3653_: *mut leanh::LeanObject,
    mut v___y_3654_: *mut leanh::LeanObject,
    mut v___y_3655_: *mut leanh::LeanObject,
    mut v___y_3656_: *mut leanh::LeanObject,
    mut v___y_3657_: *mut leanh::LeanObject,
    mut v___y_3658_: *mut leanh::LeanObject,
    mut v___y_3659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_3663_: u8 = 0;
    let mut v_zetaDeltaSet_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3670_: u8 = 0;
    let mut v_inTypeClassResolution_3671_: u8 = 0;
    let mut v_cacheInferType_3672_: u8 = 0;
    let mut v___x_3673_: u64 = 0;
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3682_: u8 = 0;
    let mut v_snd_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: u8 = 0;
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: u8 = 0;
    let mut v_arg_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: u8 = 0;
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: u8 = 0;
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v_arg_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: u8 = 0;
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: u8 = 0;
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_a_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_reuseFailAlloc_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3760_: u8 = 0;
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v_unused_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3763_: u8 = 0;
    let mut v_a_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3767_: u8 = 0;
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3661_ = l_Lean_Meta_simpGlobalConfig;
                v_config_3662_ = leanh::lean_ctor_get(v___x_3661_, 0);
                v_trackZetaDelta_3663_ = leanh::lean_ctor_get_uint8(
                    v___y_3656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3664_ = leanh::lean_ctor_get(v___y_3656_, 1);
                v_lctx_3665_ = leanh::lean_ctor_get(v___y_3656_, 2);
                v_localInstances_3666_ = leanh::lean_ctor_get(v___y_3656_, 3);
                v_defEqCtx_x3f_3667_ = leanh::lean_ctor_get(v___y_3656_, 4);
                v_synthPendingDepth_3668_ = leanh::lean_ctor_get(v___y_3656_, 5);
                v_canUnfold_x3f_3669_ = leanh::lean_ctor_get(v___y_3656_, 6);
                v_univApprox_3670_ = leanh::lean_ctor_get_uint8(
                    v___y_3656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3671_ = leanh::lean_ctor_get_uint8(
                    v___y_3656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3672_ = leanh::lean_ctor_get_uint8(
                    v___y_3656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3673_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_3662_);
                leanh::lean_inc_ref(v_config_3662_);
                v___x_3674_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3674_, 0, v_config_3662_);
                leanh::lean_ctor_set_uint64(
                    v___x_3674_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3673_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3669_);
                leanh::lean_inc(v_synthPendingDepth_3668_);
                leanh::lean_inc(v_defEqCtx_x3f_3667_);
                leanh::lean_inc_ref(v_localInstances_3666_);
                leanh::lean_inc_ref(v_lctx_3665_);
                leanh::lean_inc(v_zetaDeltaSet_3664_);
                v___x_3675_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3675_, 0, v___x_3674_);
                leanh::lean_ctor_set(v___x_3675_, 1, v_zetaDeltaSet_3664_);
                leanh::lean_ctor_set(v___x_3675_, 2, v_lctx_3665_);
                leanh::lean_ctor_set(v___x_3675_, 3, v_localInstances_3666_);
                leanh::lean_ctor_set(v___x_3675_, 4, v_defEqCtx_x3f_3667_);
                leanh::lean_ctor_set(v___x_3675_, 5, v_synthPendingDepth_3668_);
                leanh::lean_ctor_set(v___x_3675_, 6, v_canUnfold_x3f_3669_);
                leanh::lean_ctor_set_uint8(
                    v___x_3675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3663_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3670_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3671_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3672_,
                );
                v___x_3676_ = l_Lean_Meta_forallMetaTelescope(
                    v_a_3646_,
                    v___x_3647_,
                    v___x_3675_,
                    v___y_3657_,
                    v___y_3658_,
                    v___y_3659_,
                );
                leanh::lean_dec_ref_known(v___x_3675_, 7);
                if leanh::lean_obj_tag(v___x_3676_) == 0 {
                    v_a_3677_ = leanh::lean_ctor_get(v___x_3676_, 0);
                    leanh::lean_inc(v_a_3677_);
                    leanh::lean_dec_ref_known(v___x_3676_, 1);
                    v_snd_3678_ = leanh::lean_ctor_get(v_a_3677_, 1);
                    v_fst_3679_ = leanh::lean_ctor_get(v_a_3677_, 0);
                    v_isSharedCheck_3763_ = (!leanh::lean_is_exclusive(v_a_3677_)) as u8;
                    if v_isSharedCheck_3763_ == 0 {
                        v___x_3681_ = v_a_3677_;
                        v_isShared_3682_ = v_isSharedCheck_3763_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3678_);
                        leanh::lean_inc(v_fst_3679_);
                        leanh::lean_dec(v_a_3677_);
                        v___x_3681_ = leanh::lean_box(0);
                        v_isShared_3682_ = v_isSharedCheck_3763_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_prio_3653_);
                    leanh::lean_dec_ref(v_proof_3652_);
                    leanh::lean_dec_ref(v_a_3651_);
                    leanh::lean_dec_ref(v___x_3650_);
                    leanh::lean_dec_ref(v___x_3649_);
                    v_a_3764_ = leanh::lean_ctor_get(v___x_3676_, 0);
                    v_isSharedCheck_3771_ = (!leanh::lean_is_exclusive(v___x_3676_)) as u8;
                    if v_isSharedCheck_3771_ == 0 {
                        v___x_3766_ = v___x_3676_;
                        v_isShared_3767_ = v_isSharedCheck_3771_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3764_);
                        leanh::lean_dec(v___x_3676_);
                        v___x_3766_ = leanh::lean_box(0);
                        v_isShared_3767_ = v_isSharedCheck_3771_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3683_ = leanh::lean_ctor_get(v_snd_3678_, 1);
                v_isSharedCheck_3761_ = (!leanh::lean_is_exclusive(v_snd_3678_)) as u8;
                if v_isSharedCheck_3761_ == 0 {
                    v_unused_3762_ = leanh::lean_ctor_get(v_snd_3678_, 0);
                    leanh::lean_dec(v_unused_3762_);
                    v___x_3685_ = v_snd_3678_;
                    v_isShared_3686_ = v_isSharedCheck_3761_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3683_);
                    leanh::lean_dec(v_snd_3678_);
                    v___x_3685_ = leanh::lean_box(0);
                    v_isShared_3686_ = v_isSharedCheck_3761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3687_ = l_Lean_Meta_whnfR(
                    v_snd_3683_,
                    v___y_3656_,
                    v___y_3657_,
                    v___y_3658_,
                    v___y_3659_,
                );
                if leanh::lean_obj_tag(v___x_3687_) == 0 {
                    v_a_3688_ = leanh::lean_ctor_get(v___x_3687_, 0);
                    leanh::lean_inc_n(v_a_3688_, 2);
                    leanh::lean_dec_ref_known(v___x_3687_, 1);
                    v___x_3702_ = l_Lean_Expr_cleanupAnnotations(v_a_3688_);
                    v___x_3703_ = l_Lean_Expr_isApp(v___x_3702_);
                    if v___x_3703_ == 0 {
                        leanh::lean_dec_ref(v___x_3702_);
                        leanh::lean_del_object(v___x_3681_);
                        leanh::lean_dec(v_fst_3679_);
                        leanh::lean_dec(v_prio_3653_);
                        leanh::lean_dec_ref(v_proof_3652_);
                        leanh::lean_dec_ref(v_a_3651_);
                        leanh::lean_dec_ref(v___x_3650_);
                        leanh::lean_dec_ref(v___x_3649_);
                        v___y_3690_ = v___y_3654_;
                        v___y_3691_ = v___y_3655_;
                        v___y_3692_ = v___y_3656_;
                        v___y_3693_ = v___y_3657_;
                        v___y_3694_ = v___y_3658_;
                        v___y_3695_ = v___y_3659_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3704_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3702_);
                        v___x_3705_ = l_Lean_Expr_isApp(v___x_3704_);
                        if v___x_3705_ == 0 {
                            leanh::lean_dec_ref(v___x_3704_);
                            leanh::lean_del_object(v___x_3681_);
                            leanh::lean_dec(v_fst_3679_);
                            leanh::lean_dec(v_prio_3653_);
                            leanh::lean_dec_ref(v_proof_3652_);
                            leanh::lean_dec_ref(v_a_3651_);
                            leanh::lean_dec_ref(v___x_3650_);
                            leanh::lean_dec_ref(v___x_3649_);
                            v___y_3690_ = v___y_3654_;
                            v___y_3691_ = v___y_3655_;
                            v___y_3692_ = v___y_3656_;
                            v___y_3693_ = v___y_3657_;
                            v___y_3694_ = v___y_3658_;
                            v___y_3695_ = v___y_3659_;
                            state = 3;
                            continue;
                        } else {
                            v_arg_3706_ = leanh::lean_ctor_get(v___x_3704_, 1);
                            leanh::lean_inc_ref(v_arg_3706_);
                            v___x_3707_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3704_);
                            v___x_3708_ = l_Lean_Expr_isApp(v___x_3707_);
                            if v___x_3708_ == 0 {
                                leanh::lean_dec_ref(v___x_3707_);
                                leanh::lean_dec_ref(v_arg_3706_);
                                leanh::lean_del_object(v___x_3681_);
                                leanh::lean_dec(v_fst_3679_);
                                leanh::lean_dec(v_prio_3653_);
                                leanh::lean_dec_ref(v_proof_3652_);
                                leanh::lean_dec_ref(v_a_3651_);
                                leanh::lean_dec_ref(v___x_3650_);
                                leanh::lean_dec_ref(v___x_3649_);
                                v___y_3690_ = v___y_3654_;
                                v___y_3691_ = v___y_3655_;
                                v___y_3692_ = v___y_3656_;
                                v___y_3693_ = v___y_3657_;
                                v___y_3694_ = v___y_3658_;
                                v___y_3695_ = v___y_3659_;
                                state = 3;
                                continue;
                            } else {
                                v___x_3709_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3707_);
                                v___x_3710_ = l_Lean_Expr_isApp(v___x_3709_);
                                if v___x_3710_ == 0 {
                                    leanh::lean_dec_ref(v___x_3709_);
                                    leanh::lean_dec_ref(v_arg_3706_);
                                    leanh::lean_del_object(v___x_3681_);
                                    leanh::lean_dec(v_fst_3679_);
                                    leanh::lean_dec(v_prio_3653_);
                                    leanh::lean_dec_ref(v_proof_3652_);
                                    leanh::lean_dec_ref(v_a_3651_);
                                    leanh::lean_dec_ref(v___x_3650_);
                                    leanh::lean_dec_ref(v___x_3649_);
                                    v___y_3690_ = v___y_3654_;
                                    v___y_3691_ = v___y_3655_;
                                    v___y_3692_ = v___y_3656_;
                                    v___y_3693_ = v___y_3657_;
                                    v___y_3694_ = v___y_3658_;
                                    v___y_3695_ = v___y_3659_;
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3709_);
                                    v___x_3712_ = l_Lean_Expr_isApp(v___x_3711_);
                                    if v___x_3712_ == 0 {
                                        leanh::lean_dec_ref(v___x_3711_);
                                        leanh::lean_dec_ref(v_arg_3706_);
                                        leanh::lean_del_object(v___x_3681_);
                                        leanh::lean_dec(v_fst_3679_);
                                        leanh::lean_dec(v_prio_3653_);
                                        leanh::lean_dec_ref(v_proof_3652_);
                                        leanh::lean_dec_ref(v_a_3651_);
                                        leanh::lean_dec_ref(v___x_3650_);
                                        leanh::lean_dec_ref(v___x_3649_);
                                        v___y_3690_ = v___y_3654_;
                                        v___y_3691_ = v___y_3655_;
                                        v___y_3692_ = v___y_3656_;
                                        v___y_3693_ = v___y_3657_;
                                        v___y_3694_ = v___y_3658_;
                                        v___y_3695_ = v___y_3659_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3713_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3711_);
                                        v___x_3714_ = l_Lean_Expr_isApp(v___x_3713_);
                                        if v___x_3714_ == 0 {
                                            leanh::lean_dec_ref(v___x_3713_);
                                            leanh::lean_dec_ref(v_arg_3706_);
                                            leanh::lean_del_object(v___x_3681_);
                                            leanh::lean_dec(v_fst_3679_);
                                            leanh::lean_dec(v_prio_3653_);
                                            leanh::lean_dec_ref(v_proof_3652_);
                                            leanh::lean_dec_ref(v_a_3651_);
                                            leanh::lean_dec_ref(v___x_3650_);
                                            leanh::lean_dec_ref(v___x_3649_);
                                            v___y_3690_ = v___y_3654_;
                                            v___y_3691_ = v___y_3655_;
                                            v___y_3692_ = v___y_3656_;
                                            v___y_3693_ = v___y_3657_;
                                            v___y_3694_ = v___y_3658_;
                                            v___y_3695_ = v___y_3659_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v_arg_3715_ =
                                                leanh::lean_ctor_get(v___x_3713_, 1);
                                            leanh::lean_inc_ref(v_arg_3715_);
                                            v___x_3716_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3713_);
                                            v___x_3717_ = l_Lean_Expr_isApp(v___x_3716_);
                                            if v___x_3717_ == 0 {
                                                leanh::lean_dec_ref(v___x_3716_);
                                                leanh::lean_dec_ref(v_arg_3715_);
                                                leanh::lean_dec_ref(v_arg_3706_);
                                                leanh::lean_del_object(v___x_3681_);
                                                leanh::lean_dec(v_fst_3679_);
                                                leanh::lean_dec(v_prio_3653_);
                                                leanh::lean_dec_ref(v_proof_3652_);
                                                leanh::lean_dec_ref(v_a_3651_);
                                                leanh::lean_dec_ref(v___x_3650_);
                                                leanh::lean_dec_ref(v___x_3649_);
                                                v___y_3690_ = v___y_3654_;
                                                v___y_3691_ = v___y_3655_;
                                                v___y_3692_ = v___y_3656_;
                                                v___y_3693_ = v___y_3657_;
                                                v___y_3694_ = v___y_3658_;
                                                v___y_3695_ = v___y_3659_;
                                                state = 3;
                                                continue;
                                            } else {
                                                v___x_3718_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_3716_);
                                                v___x_3719_ =
                                                    l_Lean_Expr_isConstOf(v___x_3718_, v___x_3648_);
                                                if v___x_3719_ == 0 {
                                                    leanh::lean_dec_ref(v___x_3718_);
                                                    leanh::lean_dec_ref(v_arg_3715_);
                                                    leanh::lean_dec_ref(v_arg_3706_);
                                                    leanh::lean_del_object(v___x_3681_);
                                                    leanh::lean_dec(v_fst_3679_);
                                                    leanh::lean_dec(v_prio_3653_);
                                                    leanh::lean_dec_ref(v_proof_3652_);
                                                    leanh::lean_dec_ref(v_a_3651_);
                                                    leanh::lean_dec_ref(v___x_3650_);
                                                    leanh::lean_dec_ref(v___x_3649_);
                                                    v___y_3690_ = v___y_3654_;
                                                    v___y_3691_ = v___y_3655_;
                                                    v___y_3692_ = v___y_3656_;
                                                    v___y_3693_ = v___y_3657_;
                                                    v___y_3694_ = v___y_3658_;
                                                    v___y_3695_ = v___y_3659_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v_a_3688_);
                                                    leanh::lean_del_object(v___x_3685_);
                                                    v___x_3720_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__2;
                                                    v___x_3721_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__3;
                                                    v___x_3722_ = l_Lean_Name_mkStr4(
                                                        v___x_3649_,
                                                        v___x_3650_,
                                                        v___x_3720_,
                                                        v___x_3721_,
                                                    );
                                                    v___x_3723_ = leanh::lean_box(0);
                                                    v___x_3724_ =
                                                        l_Lean_Expr_constLevels_x21(v___x_3718_);
                                                    leanh::lean_dec_ref(v___x_3718_);
                                                    v___x_3725_ =
                                                        leanh::lean_unsigned_to_nat(0);
                                                    v___x_3726_ = l_List_get_x21Internal___redArg(
                                                        v___x_3723_,
                                                        v___x_3724_,
                                                        v___x_3725_,
                                                    );
                                                    leanh::lean_dec(v___x_3724_);
                                                    v___x_3727_ = leanh::lean_box(0);
                                                    if v_isShared_3682_ == 0 {
                                                        leanh::lean_ctor_set_tag(
                                                            v___x_3681_,
                                                            1,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3681_,
                                                            1,
                                                            v___x_3727_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3681_,
                                                            0,
                                                            v___x_3726_,
                                                        );
                                                        v___x_3729_ = v___x_3681_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_3752_ =
                                                            leanh::lean_alloc_ctor(
                                                                1,
                                                                2,
                                                                (0) as u32,
                                                            );
                                                        leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_3752_,
                                                            0,
                                                            v___x_3726_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_3752_,
                                                            1,
                                                            v___x_3727_,
                                                        );
                                                        v___x_3729_ = v_reuseFailAlloc_3752_;
                                                        state = 5;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_3685_);
                    leanh::lean_del_object(v___x_3681_);
                    leanh::lean_dec(v_fst_3679_);
                    leanh::lean_dec(v_prio_3653_);
                    leanh::lean_dec_ref(v_proof_3652_);
                    leanh::lean_dec_ref(v_a_3651_);
                    leanh::lean_dec_ref(v___x_3650_);
                    leanh::lean_dec_ref(v___x_3649_);
                    v_a_3753_ = leanh::lean_ctor_get(v___x_3687_, 0);
                    v_isSharedCheck_3760_ = (!leanh::lean_is_exclusive(v___x_3687_)) as u8;
                    if v_isSharedCheck_3760_ == 0 {
                        v___x_3755_ = v___x_3687_;
                        v_isShared_3756_ = v_isSharedCheck_3760_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3753_);
                        leanh::lean_dec(v___x_3687_);
                        v___x_3755_ = leanh::lean_box(0);
                        v_isShared_3756_ = v_isSharedCheck_3760_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3696_ = l_Lean_MessageData_ofExpr(v_a_3688_);
                v___x_3697_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___closed__1,
                );
                if v_isShared_3686_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3685_, 7);
                    leanh::lean_ctor_set(v___x_3685_, 1, v___x_3697_);
                    leanh::lean_ctor_set(v___x_3685_, 0, v___x_3696_);
                    v___x_3699_ = v___x_3685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3701_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3696_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3701_, 1, v___x_3697_);
                    v___x_3699_ = v_reuseFailAlloc_3701_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3700_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v___x_3699_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
                return v___x_3700_;
            }
            5 => {
                v___x_3730_ = l_Lean_mkConst(v___x_3722_, v___x_3729_);
                v___x_3731_ = l_Lean_Expr_app___override(v___x_3730_, v_arg_3715_);
                v___x_3732_ = l_Lean_Elab_Tactic_Do_SpecAttr_computeMVarBetaPotentialForSPred(
                    v_fst_3679_,
                    v___x_3731_,
                    v_arg_3706_,
                    v___y_3656_,
                    v___y_3657_,
                    v___y_3658_,
                    v___y_3659_,
                );
                if leanh::lean_obj_tag(v___x_3732_) == 0 {
                    v_a_3733_ = leanh::lean_ctor_get(v___x_3732_, 0);
                    v_isSharedCheck_3743_ = (!leanh::lean_is_exclusive(v___x_3732_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3735_ = v___x_3732_;
                        v_isShared_3736_ = v_isSharedCheck_3743_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3733_);
                        leanh::lean_dec(v___x_3732_);
                        v___x_3735_ = leanh::lean_box(0);
                        v_isShared_3736_ = v_isSharedCheck_3743_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_prio_3653_);
                    leanh::lean_dec_ref(v_proof_3652_);
                    leanh::lean_dec_ref(v_a_3651_);
                    v_a_3744_ = leanh::lean_ctor_get(v___x_3732_, 0);
                    v_isSharedCheck_3751_ = (!leanh::lean_is_exclusive(v___x_3732_)) as u8;
                    if v_isSharedCheck_3751_ == 0 {
                        v___x_3746_ = v___x_3732_;
                        v_isShared_3747_ = v_isSharedCheck_3751_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3744_);
                        leanh::lean_dec(v___x_3732_);
                        v___x_3746_ = leanh::lean_box(0);
                        v_isShared_3747_ = v_isSharedCheck_3751_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3737_, 0, v_a_3733_);
                v___x_3738_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3738_, 0, v_a_3651_);
                leanh::lean_ctor_set(v___x_3738_, 1, v_proof_3652_);
                leanh::lean_ctor_set(v___x_3738_, 2, v___x_3737_);
                leanh::lean_ctor_set(v___x_3738_, 3, v_prio_3653_);
                v___x_3739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3739_, 0, v___x_3738_);
                if v_isShared_3736_ == 0 {
                    leanh::lean_ctor_set(v___x_3735_, 0, v___x_3739_);
                    v___x_3741_ = v___x_3735_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
                    v___x_3741_ = v_reuseFailAlloc_3742_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3741_;
            }
            8 => {
                if v_isShared_3747_ == 0 {
                    v___x_3749_ = v___x_3746_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3750_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
                    v___x_3749_ = v_reuseFailAlloc_3750_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3749_;
            }
            10 => {
                if v_isShared_3756_ == 0 {
                    v___x_3758_ = v___x_3755_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
                    v___x_3758_ = v_reuseFailAlloc_3759_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3758_;
            }
            12 => {
                if v_isShared_3767_ == 0 {
                    v___x_3769_ = v___x_3766_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3770_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
                    v___x_3769_ = v_reuseFailAlloc_3770_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3769_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed(
    mut v_a_3772_: *mut leanh::LeanObject,
    mut v___x_3773_: *mut leanh::LeanObject,
    mut v___x_3774_: *mut leanh::LeanObject,
    mut v___x_3775_: *mut leanh::LeanObject,
    mut v___x_3776_: *mut leanh::LeanObject,
    mut v_a_3777_: *mut leanh::LeanObject,
    mut v_proof_3778_: *mut leanh::LeanObject,
    mut v_prio_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
    mut v___y_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___y_3785_: *mut leanh::LeanObject,
    mut v___y_3786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_16832__boxed_3787_: u8 = 0;
    let mut v_res_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_16832__boxed_3787_ = (leanh::lean_unbox(v___x_3773_) as u8);
    v_res_3788_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0(
        v_a_3772_,
        v___x_16832__boxed_3787_,
        v___x_3774_,
        v___x_3775_,
        v___x_3776_,
        v_a_3777_,
        v_proof_3778_,
        v_prio_3779_,
        v___y_3780_,
        v___y_3781_,
        v___y_3782_,
        v___y_3783_,
        v___y_3784_,
        v___y_3785_,
    );
    leanh::lean_dec(v___y_3785_);
    leanh::lean_dec_ref(v___y_3784_);
    leanh::lean_dec(v___y_3783_);
    leanh::lean_dec_ref(v___y_3782_);
    leanh::lean_dec(v___y_3781_);
    leanh::lean_dec_ref(v___y_3780_);
    leanh::lean_dec(v___x_3774_);
    return v_res_3788_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(
    mut v_proof_3789_: *mut leanh::LeanObject,
    mut v_prio_3790_: *mut leanh::LeanObject,
    mut v_a_3791_: *mut leanh::LeanObject,
    mut v_a_3792_: *mut leanh::LeanObject,
    mut v_a_3793_: *mut leanh::LeanObject,
    mut v_a_3794_: *mut leanh::LeanObject,
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3829_: u8 = 0;
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_a_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_a_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_proof_3789_);
                v___x_3798_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_getProof(
                    v_proof_3789_,
                    v_a_3793_,
                    v_a_3794_,
                    v_a_3795_,
                    v_a_3796_,
                );
                if leanh::lean_obj_tag(v___x_3798_) == 0 {
                    v_a_3799_ = leanh::lean_ctor_get(v___x_3798_, 0);
                    leanh::lean_inc(v_a_3799_);
                    leanh::lean_dec_ref_known(v___x_3798_, 1);
                    v_fst_3800_ = leanh::lean_ctor_get(v_a_3799_, 0);
                    leanh::lean_inc(v_fst_3800_);
                    v_snd_3801_ = leanh::lean_ctor_get(v_a_3799_, 1);
                    leanh::lean_inc_n(v_snd_3801_, 2);
                    leanh::lean_dec(v_a_3799_);
                    leanh::lean_inc(v_a_3796_);
                    leanh::lean_inc_ref(v_a_3795_);
                    leanh::lean_inc(v_a_3794_);
                    leanh::lean_inc_ref(v_a_3793_);
                    v___x_3802_ =
                        lean_infer_type(v_snd_3801_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
                    if leanh::lean_obj_tag(v___x_3802_) == 0 {
                        v_a_3803_ = leanh::lean_ctor_get(v___x_3802_, 0);
                        leanh::lean_inc(v_a_3803_);
                        leanh::lean_dec_ref_known(v___x_3802_, 1);
                        v___x_3804_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_a_3803_, v_a_3794_);
                        v_a_3805_ = leanh::lean_ctor_get(v___x_3804_, 0);
                        v_isSharedCheck_3834_ =
                            (!leanh::lean_is_exclusive(v___x_3804_)) as u8;
                        if v_isSharedCheck_3834_ == 0 {
                            v___x_3807_ = v___x_3804_;
                            v_isShared_3808_ = v_isSharedCheck_3834_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3805_);
                            leanh::lean_dec(v___x_3804_);
                            v___x_3807_ = leanh::lean_box(0);
                            v_isShared_3808_ = v_isSharedCheck_3834_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3801_);
                        leanh::lean_dec(v_fst_3800_);
                        leanh::lean_dec(v_prio_3790_);
                        leanh::lean_dec_ref(v_proof_3789_);
                        v_a_3835_ = leanh::lean_ctor_get(v___x_3802_, 0);
                        v_isSharedCheck_3842_ =
                            (!leanh::lean_is_exclusive(v___x_3802_)) as u8;
                        if v_isSharedCheck_3842_ == 0 {
                            v___x_3837_ = v___x_3802_;
                            v_isShared_3838_ = v_isSharedCheck_3842_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3835_);
                            leanh::lean_dec(v___x_3802_);
                            v___x_3837_ = leanh::lean_box(0);
                            v_isShared_3838_ = v_isSharedCheck_3842_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_prio_3790_);
                    leanh::lean_dec_ref(v_proof_3789_);
                    v_a_3843_ = leanh::lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3850_ = (!leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3850_ == 0 {
                        v___x_3845_ = v___x_3798_;
                        v_isShared_3846_ = v_isSharedCheck_3850_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3843_);
                        leanh::lean_dec(v___x_3798_);
                        v___x_3845_ = leanh::lean_box(0);
                        v_isShared_3846_ = v_isSharedCheck_3850_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3809_ = l_Lean_Expr_getForallBody(v_a_3805_);
                v___x_3810_ = l_Lean_Expr_getAppFn(v___x_3809_);
                leanh::lean_dec_ref(v___x_3809_);
                v___x_3811_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__2;
                v___x_3812_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__3;
                v___x_3813_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___lam__0___closed__5;
                v___x_3814_ = l_Lean_Expr_isConstOf(v___x_3810_, v___x_3813_);
                leanh::lean_dec_ref(v___x_3810_);
                if v___x_3814_ == 0 {
                    leanh::lean_dec(v_a_3805_);
                    leanh::lean_dec(v_snd_3801_);
                    leanh::lean_dec(v_fst_3800_);
                    leanh::lean_dec(v_prio_3790_);
                    leanh::lean_dec_ref(v_proof_3789_);
                    v___x_3815_ = leanh::lean_box(0);
                    if v_isShared_3808_ == 0 {
                        leanh::lean_ctor_set(v___x_3807_, 0, v___x_3815_);
                        v___x_3817_ = v___x_3807_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3818_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
                        v___x_3817_ = v_reuseFailAlloc_3818_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3807_);
                    v___x_3819_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg(
                        v_snd_3801_,
                        v_fst_3800_,
                        v_a_3793_,
                        v_a_3794_,
                        v_a_3795_,
                        v_a_3796_,
                    );
                    if leanh::lean_obj_tag(v___x_3819_) == 0 {
                        v_a_3820_ = leanh::lean_ctor_get(v___x_3819_, 0);
                        leanh::lean_inc(v_a_3820_);
                        leanh::lean_dec_ref_known(v___x_3819_, 1);
                        v___x_3821_ = 0;
                        v___x_3822_ = leanh::lean_box((v___x_3821_) as usize);
                        v___f_3823_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___lam__0___boxed
                                as *mut core::ffi::c_void,
                            15,
                            8,
                        );
                        leanh::lean_closure_set(v___f_3823_, 0, v_a_3805_);
                        leanh::lean_closure_set(v___f_3823_, 1, v___x_3822_);
                        leanh::lean_closure_set(v___f_3823_, 2, v___x_3813_);
                        leanh::lean_closure_set(v___f_3823_, 3, v___x_3811_);
                        leanh::lean_closure_set(v___f_3823_, 4, v___x_3812_);
                        leanh::lean_closure_set(v___f_3823_, 5, v_a_3820_);
                        leanh::lean_closure_set(v___f_3823_, 6, v_proof_3789_);
                        leanh::lean_closure_set(v___f_3823_, 7, v_prio_3790_);
                        v___x_3824_ = 0;
                        v___x_3825_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__2___redArg(v___f_3823_, v___x_3824_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_);
                        return v___x_3825_;
                    } else {
                        leanh::lean_dec(v_a_3805_);
                        leanh::lean_dec(v_prio_3790_);
                        leanh::lean_dec_ref(v_proof_3789_);
                        v_a_3826_ = leanh::lean_ctor_get(v___x_3819_, 0);
                        v_isSharedCheck_3833_ =
                            (!leanh::lean_is_exclusive(v___x_3819_)) as u8;
                        if v_isSharedCheck_3833_ == 0 {
                            v___x_3828_ = v___x_3819_;
                            v_isShared_3829_ = v_isSharedCheck_3833_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3826_);
                            leanh::lean_dec(v___x_3819_);
                            v___x_3828_ = leanh::lean_box(0);
                            v_isShared_3829_ = v_isSharedCheck_3833_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3817_;
            }
            3 => {
                if v_isShared_3829_ == 0 {
                    v___x_3831_ = v___x_3828_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
                    v___x_3831_ = v_reuseFailAlloc_3832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3831_;
            }
            5 => {
                if v_isShared_3838_ == 0 {
                    v___x_3840_ = v___x_3837_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
                    v___x_3840_ = v_reuseFailAlloc_3841_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3840_;
            }
            7 => {
                if v_isShared_3846_ == 0 {
                    v___x_3848_ = v___x_3845_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3849_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
                    v___x_3848_ = v_reuseFailAlloc_3849_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew___boxed(
    mut v_proof_3851_: *mut leanh::LeanObject,
    mut v_prio_3852_: *mut leanh::LeanObject,
    mut v_a_3853_: *mut leanh::LeanObject,
    mut v_a_3854_: *mut leanh::LeanObject,
    mut v_a_3855_: *mut leanh::LeanObject,
    mut v_a_3856_: *mut leanh::LeanObject,
    mut v_a_3857_: *mut leanh::LeanObject,
    mut v_a_3858_: *mut leanh::LeanObject,
    mut v_a_3859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3860_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(
        v_proof_3851_,
        v_prio_3852_,
        v_a_3853_,
        v_a_3854_,
        v_a_3855_,
        v_a_3856_,
        v_a_3857_,
        v_a_3858_,
    );
    leanh::lean_dec(v_a_3858_);
    leanh::lean_dec_ref(v_a_3857_);
    leanh::lean_dec(v_a_3856_);
    leanh::lean_dec_ref(v_a_3855_);
    leanh::lean_dec(v_a_3854_);
    leanh::lean_dec_ref(v_a_3853_);
    return v_res_3860_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1(
    mut v_00_u03b1_3861_: *mut leanh::LeanObject,
    mut v_msg_3862_: *mut leanh::LeanObject,
    mut v___y_3863_: *mut leanh::LeanObject,
    mut v___y_3864_: *mut leanh::LeanObject,
    mut v___y_3865_: *mut leanh::LeanObject,
    mut v___y_3866_: *mut leanh::LeanObject,
    mut v___y_3867_: *mut leanh::LeanObject,
    mut v___y_3868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(
            v_msg_3862_,
            v___y_3865_,
            v___y_3866_,
            v___y_3867_,
            v___y_3868_,
        );
    return v___x_3870_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___boxed(
    mut v_00_u03b1_3871_: *mut leanh::LeanObject,
    mut v_msg_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
    mut v___y_3874_: *mut leanh::LeanObject,
    mut v___y_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
    mut v___y_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3880_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1(
        v_00_u03b1_3871_,
        v_msg_3872_,
        v___y_3873_,
        v___y_3874_,
        v___y_3875_,
        v___y_3876_,
        v___y_3877_,
        v___y_3878_,
    );
    leanh::lean_dec(v___y_3878_);
    leanh::lean_dec_ref(v___y_3877_);
    leanh::lean_dec(v___y_3876_);
    leanh::lean_dec_ref(v___y_3875_);
    leanh::lean_dec(v___y_3874_);
    leanh::lean_dec_ref(v___y_3873_);
    return v_res_3880_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern_collectDomains(
    mut v_ty_3881_: *mut leanh::LeanObject,
    mut v_acc_3882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_binderType_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_ty_3881_) == 7 {
                    v_binderType_3883_ = leanh::lean_ctor_get(v_ty_3881_, 1);
                    leanh::lean_inc_ref(v_binderType_3883_);
                    v_body_3884_ = leanh::lean_ctor_get(v_ty_3881_, 2);
                    leanh::lean_inc_ref(v_body_3884_);
                    leanh::lean_dec_ref_known(v_ty_3881_, 3);
                    v___x_3885_ = lean_array_push(v_acc_3882_, v_binderType_3883_);
                    v_ty_3881_ = v_body_3884_;
                    v_acc_3882_ = v___x_3885_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_ty_3881_);
                    return v_acc_3882_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0(
    mut v_k_3887_: *mut leanh::LeanObject,
    mut v_i_3888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3889_ = leanh::lean_unsigned_to_nat(1);
    v___x_3890_ = lean_nat_sub(v_k_3887_, v___x_3889_);
    v___x_3891_ = lean_nat_sub(v___x_3890_, v_i_3888_);
    leanh::lean_dec(v___x_3890_);
    v___x_3892_ = l_Lean_mkBVar(v___x_3891_);
    return v___x_3892_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0___boxed(
    mut v_k_3893_: *mut leanh::LeanObject,
    mut v_i_3894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3895_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0(v_k_3893_, v_i_3894_);
    leanh::lean_dec(v_i_3894_);
    leanh::lean_dec(v_k_3893_);
    return v_res_3895_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern(
    mut v_pattern_3896_: *mut leanh::LeanObject,
    mut v_eqTy_3897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3898_: u8 = 0;
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varTypes_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnInfos_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extraDomains_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_liftedPattern_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newBVars_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newPatternExpr_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newPattern_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut v_unused_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3898_ = l_Lean_Expr_isForall(v_eqTy_3897_);
                if v___x_3898_ == 0 {
                    leanh::lean_dec_ref(v_eqTy_3897_);
                    v___x_3899_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3900_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3900_, 0, v_pattern_3896_);
                    leanh::lean_ctor_set(v___x_3900_, 1, v___x_3899_);
                    return v___x_3900_;
                } else {
                    v_levelParams_3901_ = leanh::lean_ctor_get(v_pattern_3896_, 0);
                    v_varTypes_3902_ = leanh::lean_ctor_get(v_pattern_3896_, 1);
                    v_pattern_3903_ = leanh::lean_ctor_get(v_pattern_3896_, 3);
                    v_fnInfos_3904_ = leanh::lean_ctor_get(v_pattern_3896_, 4);
                    v_isSharedCheck_3922_ =
                        (!leanh::lean_is_exclusive(v_pattern_3896_)) as u8;
                    if v_isSharedCheck_3922_ == 0 {
                        v_unused_3923_ = leanh::lean_ctor_get(v_pattern_3896_, 5);
                        leanh::lean_dec(v_unused_3923_);
                        v_unused_3924_ = leanh::lean_ctor_get(v_pattern_3896_, 2);
                        leanh::lean_dec(v_unused_3924_);
                        v___x_3906_ = v_pattern_3896_;
                        v_isShared_3907_ = v_isSharedCheck_3922_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fnInfos_3904_);
                        leanh::lean_inc(v_pattern_3903_);
                        leanh::lean_inc(v_varTypes_3902_);
                        leanh::lean_inc(v_levelParams_3901_);
                        leanh::lean_dec(v_pattern_3896_);
                        v___x_3906_ = leanh::lean_box(0);
                        v_isShared_3907_ = v_isSharedCheck_3922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3908_ = leanh::lean_unsigned_to_nat(0);
                v___x_3909_ =
                    l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1;
                v_extraDomains_3910_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern_collectDomains(v_eqTy_3897_, v___x_3909_);
                v_k_3911_ = lean_array_get_size(v_extraDomains_3910_);
                v___f_3912_ = leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_3912_, 0, v_k_3911_);
                v_liftedPattern_3913_ =
                    lean_expr_lift_loose_bvars(v_pattern_3903_, v___x_3908_, v_k_3911_);
                leanh::lean_dec_ref(v_pattern_3903_);
                v_newBVars_3914_ = l_Array_ofFn___redArg(v_k_3911_, v___f_3912_);
                v_newPatternExpr_3915_ = l_Lean_mkAppN(v_liftedPattern_3913_, v_newBVars_3914_);
                leanh::lean_dec_ref(v_newBVars_3914_);
                v___x_3916_ = l_Array_append___redArg(v_varTypes_3902_, v_extraDomains_3910_);
                leanh::lean_dec_ref(v_extraDomains_3910_);
                v___x_3917_ = leanh::lean_box(0);
                if v_isShared_3907_ == 0 {
                    leanh::lean_ctor_set(v___x_3906_, 5, v___x_3917_);
                    leanh::lean_ctor_set(v___x_3906_, 3, v_newPatternExpr_3915_);
                    leanh::lean_ctor_set(v___x_3906_, 2, v___x_3917_);
                    leanh::lean_ctor_set(v___x_3906_, 1, v___x_3916_);
                    v_newPattern_3919_ = v___x_3906_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3921_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_levelParams_3901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___x_3916_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 2, v___x_3917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 3, v_newPatternExpr_3915_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 4, v_fnInfos_3904_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3921_, 5, v___x_3917_);
                    v_newPattern_3919_ = v_reuseFailAlloc_3921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3920_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3920_, 0, v_newPattern_3919_);
                leanh::lean_ctor_set(v___x_3920_, 1, v_k_3911_);
                return v___x_3920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3926_ =
        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__0;
    v___x_3927_ = l_Lean_stringToMessageData(v___x_3926_);
    return v___x_3927_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0(
    mut v_body_3928_: *mut leanh::LeanObject,
    mut v___y_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: u8 = 0;
    let mut v_arg_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: u8 = 0;
    let mut v_arg_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: u8 = 0;
    let mut v_arg_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_body_3928_);
                v___x_3939_ = l_Lean_Expr_cleanupAnnotations(v_body_3928_);
                v___x_3940_ = l_Lean_Expr_isApp(v___x_3939_);
                if v___x_3940_ == 0 {
                    leanh::lean_dec_ref(v___x_3939_);
                    state = 1;
                    continue;
                } else {
                    v_arg_3941_ = leanh::lean_ctor_get(v___x_3939_, 1);
                    leanh::lean_inc_ref(v_arg_3941_);
                    v___x_3942_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3939_);
                    v___x_3943_ = l_Lean_Expr_isApp(v___x_3942_);
                    if v___x_3943_ == 0 {
                        leanh::lean_dec_ref(v___x_3942_);
                        leanh::lean_dec_ref(v_arg_3941_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_3944_ = leanh::lean_ctor_get(v___x_3942_, 1);
                        leanh::lean_inc_ref(v_arg_3944_);
                        v___x_3945_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3942_);
                        v___x_3946_ = l_Lean_Expr_isApp(v___x_3945_);
                        if v___x_3946_ == 0 {
                            leanh::lean_dec_ref(v___x_3945_);
                            leanh::lean_dec_ref(v_arg_3944_);
                            leanh::lean_dec_ref(v_arg_3941_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_3947_ = leanh::lean_ctor_get(v___x_3945_, 1);
                            leanh::lean_inc_ref(v_arg_3947_);
                            v___x_3948_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3945_);
                            v___x_3949_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremNew_instantiate___closed__1;
                            v___x_3950_ = l_Lean_Expr_isConstOf(v___x_3948_, v___x_3949_);
                            leanh::lean_dec_ref(v___x_3948_);
                            if v___x_3950_ == 0 {
                                leanh::lean_dec_ref(v_arg_3947_);
                                leanh::lean_dec_ref(v_arg_3944_);
                                leanh::lean_dec_ref(v_arg_3941_);
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_body_3928_);
                                v___x_3951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3951_, 0, v_arg_3947_);
                                leanh::lean_ctor_set(v___x_3951_, 1, v_arg_3941_);
                                v___x_3952_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3952_, 0, v_arg_3944_);
                                leanh::lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                                v___x_3953_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3953_, 0, v___x_3952_);
                                return v___x_3953_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3935_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___closed__1);
                v___x_3936_ = l_Lean_indentExpr(v_body_3928_);
                v___x_3937_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3937_, 0, v___x_3935_);
                leanh::lean_ctor_set(v___x_3937_, 1, v___x_3936_);
                v___x_3938_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0___redArg(v___x_3937_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
                return v___x_3938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0___boxed(
    mut v_body_3954_: *mut leanh::LeanObject,
    mut v___y_3955_: *mut leanh::LeanObject,
    mut v___y_3956_: *mut leanh::LeanObject,
    mut v___y_3957_: *mut leanh::LeanObject,
    mut v___y_3958_: *mut leanh::LeanObject,
    mut v___y_3959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3960_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___lam__0(
        v_body_3954_,
        v___y_3955_,
        v___y_3956_,
        v___y_3957_,
        v___y_3958_,
    );
    leanh::lean_dec(v___y_3958_);
    leanh::lean_dec_ref(v___y_3957_);
    leanh::lean_dec(v___y_3956_);
    leanh::lean_dec_ref(v___y_3955_);
    return v_res_3960_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(
    mut v_declName_3962_: *mut leanh::LeanObject,
    mut v_prio_3963_: *mut leanh::LeanObject,
    mut v_a_3964_: *mut leanh::LeanObject,
    mut v_a_3965_: *mut leanh::LeanObject,
    mut v_a_3966_: *mut leanh::LeanObject,
    mut v_a_3967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3980_: u8 = 0;
    let mut v_snd_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3989_: u8 = 0;
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v_pattern_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: u8 = 0;
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut v_a_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_a_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4016_: u8 = 0;
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_3962_);
                v___x_3969_ =
                    l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_preprocessDeclPattern(
                        v_declName_3962_,
                        v_a_3964_,
                        v_a_3965_,
                        v_a_3966_,
                        v_a_3967_,
                    );
                if leanh::lean_obj_tag(v___x_3969_) == 0 {
                    v_a_3970_ = leanh::lean_ctor_get(v___x_3969_, 0);
                    leanh::lean_inc(v_a_3970_);
                    leanh::lean_dec_ref_known(v___x_3969_, 1);
                    v_fst_3971_ = leanh::lean_ctor_get(v_a_3970_, 0);
                    leanh::lean_inc(v_fst_3971_);
                    v_snd_3972_ = leanh::lean_ctor_get(v_a_3970_, 1);
                    leanh::lean_inc_n(v_snd_3972_, 2);
                    leanh::lean_dec(v_a_3970_);
                    v___f_3973_ =
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___closed__0;
                    v___x_3974_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3975_ =
                        l_Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr___redArg___closed__1;
                    v___x_3976_ = l___private_Lean_Meta_Sym_Pattern_0__Lean_Meta_Sym_mkPatternFromTypeWithKey_go(leanh::lean_box(0), v_fst_3971_, v_snd_3972_, v___f_3973_, v_snd_3972_, v___x_3975_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_);
                    if leanh::lean_obj_tag(v___x_3976_) == 0 {
                        v_a_3977_ = leanh::lean_ctor_get(v___x_3976_, 0);
                        v_isSharedCheck_4004_ =
                            (!leanh::lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_4004_ == 0 {
                            v___x_3979_ = v___x_3976_;
                            v_isShared_3980_ = v_isSharedCheck_4004_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3977_);
                            leanh::lean_dec(v___x_3976_);
                            v___x_3979_ = leanh::lean_box(0);
                            v_isShared_3980_ = v_isSharedCheck_4004_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_prio_3963_);
                        leanh::lean_dec(v_declName_3962_);
                        v_a_4005_ = leanh::lean_ctor_get(v___x_3976_, 0);
                        v_isSharedCheck_4012_ =
                            (!leanh::lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_4012_ == 0 {
                            v___x_4007_ = v___x_3976_;
                            v_isShared_4008_ = v_isSharedCheck_4012_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4005_);
                            leanh::lean_dec(v___x_3976_);
                            v___x_4007_ = leanh::lean_box(0);
                            v_isShared_4008_ = v_isSharedCheck_4012_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_prio_3963_);
                    leanh::lean_dec(v_declName_3962_);
                    v_a_4013_ = leanh::lean_ctor_get(v___x_3969_, 0);
                    v_isSharedCheck_4020_ = (!leanh::lean_is_exclusive(v___x_3969_)) as u8;
                    if v_isSharedCheck_4020_ == 0 {
                        v___x_4015_ = v___x_3969_;
                        v_isShared_4016_ = v_isSharedCheck_4020_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4013_);
                        leanh::lean_dec(v___x_3969_);
                        v___x_4015_ = leanh::lean_box(0);
                        v_isShared_4016_ = v_isSharedCheck_4020_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_3981_ = leanh::lean_ctor_get(v_a_3977_, 1);
                leanh::lean_inc(v_snd_3981_);
                v_fst_3982_ = leanh::lean_ctor_get(v_a_3977_, 0);
                leanh::lean_inc(v_fst_3982_);
                leanh::lean_dec(v_a_3977_);
                v_fst_3983_ = leanh::lean_ctor_get(v_snd_3981_, 0);
                leanh::lean_inc(v_fst_3983_);
                v_snd_3984_ = leanh::lean_ctor_get(v_snd_3981_, 1);
                leanh::lean_inc(v_snd_3984_);
                leanh::lean_dec(v_snd_3981_);
                v___x_3985_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB_0__Lean_Elab_Tactic_Do_SpecAttr_etaExpandEqPattern(v_fst_3982_, v_fst_3983_);
                v_fst_3986_ = leanh::lean_ctor_get(v___x_3985_, 0);
                leanh::lean_inc(v_fst_3986_);
                v_snd_3987_ = leanh::lean_ctor_get(v___x_3985_, 1);
                leanh::lean_inc(v_snd_3987_);
                leanh::lean_dec_ref(v___x_3985_);
                v___x_4001_ = lean_nat_dec_eq(v_snd_3987_, v___x_3974_);
                if v___x_4001_ == 0 {
                    leanh::lean_dec(v_snd_3984_);
                    v___y_3989_ = v___x_4001_;
                    state = 2;
                    continue;
                } else {
                    v_pattern_4002_ = leanh::lean_ctor_get(v_fst_3986_, 3);
                    v___x_4003_ = lean_expr_eqv(v_pattern_4002_, v_snd_3984_);
                    leanh::lean_dec(v_snd_3984_);
                    v___y_3989_ = v___x_4003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_3989_ == 0 {
                    v___x_3990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3990_, 0, v_declName_3962_);
                    v___x_3991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3991_, 0, v_snd_3987_);
                    v___x_3992_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_3992_, 0, v_fst_3986_);
                    leanh::lean_ctor_set(v___x_3992_, 1, v___x_3990_);
                    leanh::lean_ctor_set(v___x_3992_, 2, v___x_3991_);
                    leanh::lean_ctor_set(v___x_3992_, 3, v_prio_3963_);
                    v___x_3993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3993_, 0, v___x_3992_);
                    if v_isShared_3980_ == 0 {
                        leanh::lean_ctor_set(v___x_3979_, 0, v___x_3993_);
                        v___x_3995_ = v___x_3979_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3996_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
                        v___x_3995_ = v_reuseFailAlloc_3996_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3987_);
                    leanh::lean_dec(v_fst_3986_);
                    leanh::lean_dec(v_prio_3963_);
                    leanh::lean_dec(v_declName_3962_);
                    v___x_3997_ = leanh::lean_box(0);
                    if v_isShared_3980_ == 0 {
                        leanh::lean_ctor_set(v___x_3979_, 0, v___x_3997_);
                        v___x_3999_ = v___x_3979_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4000_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3997_);
                        v___x_3999_ = v_reuseFailAlloc_4000_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3995_;
            }
            4 => {
                return v___x_3999_;
            }
            5 => {
                if v_isShared_4008_ == 0 {
                    v___x_4010_ = v___x_4007_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
                    v___x_4010_ = v_reuseFailAlloc_4011_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4010_;
            }
            7 => {
                if v_isShared_4016_ == 0 {
                    v___x_4018_ = v___x_4015_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4019_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
                    v___x_4018_ = v_reuseFailAlloc_4019_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f___boxed(
    mut v_declName_4021_: *mut leanh::LeanObject,
    mut v_prio_4022_: *mut leanh::LeanObject,
    mut v_a_4023_: *mut leanh::LeanObject,
    mut v_a_4024_: *mut leanh::LeanObject,
    mut v_a_4025_: *mut leanh::LeanObject,
    mut v_a_4026_: *mut leanh::LeanObject,
    mut v_a_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4028_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(
        v_declName_4021_,
        v_prio_4022_,
        v_a_4023_,
        v_a_4024_,
        v_a_4025_,
        v_a_4026_,
    );
    leanh::lean_dec(v_a_4026_);
    leanh::lean_dec_ref(v_a_4025_);
    leanh::lean_dec(v_a_4024_);
    leanh::lean_dec_ref(v_a_4023_);
    return v_res_4028_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__0(
    mut v_x1_4029_: *mut leanh::LeanObject,
    mut v_x2_4030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4031_ = lean_array_push(v_x1_4029_, v_x2_4030_);
    return v___x_4031_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(
    mut v_f_4032_: *mut leanh::LeanObject,
    mut v_as_4033_: *mut leanh::LeanObject,
    mut v_i_4034_: usize,
    mut v_stop_4035_: usize,
    mut v_b_4036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4037_: u8 = 0;
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: usize = 0;
    let mut v___x_4041_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4037_ = lean_usize_dec_eq(v_i_4034_, v_stop_4035_);
                if v___x_4037_ == 0 {
                    v___x_4038_ = lean_array_uget_borrowed(v_as_4033_, v_i_4034_);
                    leanh::lean_inc(v_f_4032_);
                    leanh::lean_inc(v___x_4038_);
                    v___x_4039_ = leanh::lean_apply_2(v_f_4032_, v_b_4036_, v___x_4038_);
                    v___x_4040_ = 1usize;
                    v___x_4041_ = lean_usize_add(v_i_4034_, v___x_4040_);
                    v_i_4034_ = v___x_4041_;
                    v_b_4036_ = v___x_4039_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_f_4032_);
                    return v_b_4036_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg___boxed(
    mut v_f_4043_: *mut leanh::LeanObject,
    mut v_as_4044_: *mut leanh::LeanObject,
    mut v_i_4045_: *mut leanh::LeanObject,
    mut v_stop_4046_: *mut leanh::LeanObject,
    mut v_b_4047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4048_: usize = 0;
    let mut v_stop_boxed_4049_: usize = 0;
    let mut v_res_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4048_ = leanh::lean_unbox_usize(v_i_4045_);
    leanh::lean_dec(v_i_4045_);
    v_stop_boxed_4049_ = leanh::lean_unbox_usize(v_stop_4046_);
    leanh::lean_dec(v_stop_4046_);
    v_res_4050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_4043_, v_as_4044_, v_i_boxed_4048_, v_stop_boxed_4049_, v_b_4047_);
    leanh::lean_dec_ref(v_as_4044_);
    return v_res_4050_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(
    mut v_f_4051_: *mut leanh::LeanObject,
    mut v_x_4052_: *mut leanh::LeanObject,
    mut v_x_4053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: u8 = 0;
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: usize = 0;
    let mut v___x_4063_: usize = 0;
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: usize = 0;
    let mut v___x_4066_: usize = 0;
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4073_: usize = 0;
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: usize = 0;
    let mut v___x_4077_: usize = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: usize = 0;
    let mut v___x_4081_: usize = 0;
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: usize = 0;
    let mut v___x_4084_: usize = 0;
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_4054_ = leanh::lean_ctor_get(v_x_4053_, 0);
                v_children_4055_ = leanh::lean_ctor_get(v_x_4053_, 1);
                v___x_4056_ = leanh::lean_unsigned_to_nat(0);
                v___x_4068_ = lean_array_get_size(v_vs_4054_);
                v___x_4069_ = lean_nat_dec_lt(v___x_4056_, v___x_4068_);
                if v___x_4069_ == 0 {
                    v___x_4070_ = lean_array_get_size(v_children_4055_);
                    v___x_4071_ = lean_nat_dec_lt(v___x_4056_, v___x_4070_);
                    if v___x_4071_ == 0 {
                        leanh::lean_dec(v_f_4051_);
                        return v_x_4052_;
                    } else {
                        v___x_4072_ = lean_nat_dec_le(v___x_4070_, v___x_4070_);
                        if v___x_4072_ == 0 {
                            if v___x_4071_ == 0 {
                                leanh::lean_dec(v_f_4051_);
                                return v_x_4052_;
                            } else {
                                v___x_4073_ = 0usize;
                                v___x_4074_ = lean_usize_of_nat(v___x_4070_);
                                v___x_4075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_4051_, v_children_4055_, v___x_4073_, v___x_4074_, v_x_4052_);
                                return v___x_4075_;
                            }
                        } else {
                            v___x_4076_ = 0usize;
                            v___x_4077_ = lean_usize_of_nat(v___x_4070_);
                            v___x_4078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_4051_, v_children_4055_, v___x_4076_, v___x_4077_, v_x_4052_);
                            return v___x_4078_;
                        }
                    }
                } else {
                    v___x_4079_ = lean_nat_dec_le(v___x_4068_, v___x_4068_);
                    if v___x_4079_ == 0 {
                        if v___x_4069_ == 0 {
                            v_s_4058_ = v_x_4052_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4080_ = 0usize;
                            v___x_4081_ = lean_usize_of_nat(v___x_4068_);
                            leanh::lean_inc(v_f_4051_);
                            v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_4051_, v_vs_4054_, v___x_4080_, v___x_4081_, v_x_4052_);
                            v_s_4058_ = v___x_4082_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_4083_ = 0usize;
                        v___x_4084_ = lean_usize_of_nat(v___x_4068_);
                        leanh::lean_inc(v_f_4051_);
                        v___x_4085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_4051_, v_vs_4054_, v___x_4083_, v___x_4084_, v_x_4052_);
                        v_s_4058_ = v___x_4085_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4059_ = lean_array_get_size(v_children_4055_);
                v___x_4060_ = lean_nat_dec_lt(v___x_4056_, v___x_4059_);
                if v___x_4060_ == 0 {
                    leanh::lean_dec(v_f_4051_);
                    return v_s_4058_;
                } else {
                    v___x_4061_ = lean_nat_dec_le(v___x_4059_, v___x_4059_);
                    if v___x_4061_ == 0 {
                        if v___x_4060_ == 0 {
                            leanh::lean_dec(v_f_4051_);
                            return v_s_4058_;
                        } else {
                            v___x_4062_ = 0usize;
                            v___x_4063_ = lean_usize_of_nat(v___x_4059_);
                            v___x_4064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_4051_, v_children_4055_, v___x_4062_, v___x_4063_, v_s_4058_);
                            return v___x_4064_;
                        }
                    } else {
                        v___x_4065_ = 0usize;
                        v___x_4066_ = lean_usize_of_nat(v___x_4059_);
                        v___x_4067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_4051_, v_children_4055_, v___x_4065_, v___x_4066_, v_s_4058_);
                        return v___x_4067_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(
    mut v_f_4086_: *mut leanh::LeanObject,
    mut v_as_4087_: *mut leanh::LeanObject,
    mut v_i_4088_: usize,
    mut v_stop_4089_: usize,
    mut v_b_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4091_: u8 = 0;
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: usize = 0;
    let mut v___x_4096_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4091_ = lean_usize_dec_eq(v_i_4088_, v_stop_4089_);
                if v___x_4091_ == 0 {
                    v___x_4092_ = lean_array_uget_borrowed(v_as_4087_, v_i_4088_);
                    v_snd_4093_ = leanh::lean_ctor_get(v___x_4092_, 1);
                    leanh::lean_inc(v_f_4086_);
                    v___x_4094_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_4086_, v_b_4090_, v_snd_4093_);
                    v___x_4095_ = 1usize;
                    v___x_4096_ = lean_usize_add(v_i_4088_, v___x_4095_);
                    v_i_4088_ = v___x_4096_;
                    v_b_4090_ = v___x_4094_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_f_4086_);
                    return v_b_4090_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg___boxed(
    mut v_f_4098_: *mut leanh::LeanObject,
    mut v_as_4099_: *mut leanh::LeanObject,
    mut v_i_4100_: *mut leanh::LeanObject,
    mut v_stop_4101_: *mut leanh::LeanObject,
    mut v_b_4102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4103_: usize = 0;
    let mut v_stop_boxed_4104_: usize = 0;
    let mut v_res_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4103_ = leanh::lean_unbox_usize(v_i_4100_);
    leanh::lean_dec(v_i_4100_);
    v_stop_boxed_4104_ = leanh::lean_unbox_usize(v_stop_4101_);
    leanh::lean_dec(v_stop_4101_);
    v_res_4105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_4098_, v_as_4099_, v_i_boxed_4103_, v_stop_boxed_4104_, v_b_4102_);
    leanh::lean_dec_ref(v_as_4099_);
    return v_res_4105_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg___boxed(
    mut v_f_4106_: *mut leanh::LeanObject,
    mut v_x_4107_: *mut leanh::LeanObject,
    mut v_x_4108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4109_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_4106_, v_x_4107_, v_x_4108_);
    leanh::lean_dec_ref(v_x_4108_);
    return v_res_4109_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1(
    mut v___f_4110_: *mut leanh::LeanObject,
    mut v_s_4111_: *mut leanh::LeanObject,
    mut v_x_4112_: *mut leanh::LeanObject,
    mut v_t_4113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v___f_4110_, v_s_4111_, v_t_4113_);
    return v___x_4114_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1___boxed(
    mut v___f_4115_: *mut leanh::LeanObject,
    mut v_s_4116_: *mut leanh::LeanObject,
    mut v_x_4117_: *mut leanh::LeanObject,
    mut v_t_4118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__1(
        v___f_4115_,
        v_s_4116_,
        v_x_4117_,
        v_t_4118_,
    );
    leanh::lean_dec_ref(v_t_4118_);
    leanh::lean_dec(v_x_4117_);
    return v_res_4119_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__2(
    mut v_x1_4120_: *mut leanh::LeanObject,
    mut v_x2_4121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4122_ = lean_array_push(v_x1_4120_, v_x2_4121_);
    return v___x_4122_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3(
    mut v___f_4123_: *mut leanh::LeanObject,
    mut v_s_4124_: *mut leanh::LeanObject,
    mut v_x_4125_: *mut leanh::LeanObject,
    mut v_t_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v___f_4123_, v_s_4124_, v_t_4126_);
    return v___x_4127_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3___boxed(
    mut v___f_4128_: *mut leanh::LeanObject,
    mut v_s_4129_: *mut leanh::LeanObject,
    mut v_x_4130_: *mut leanh::LeanObject,
    mut v_t_4131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4132_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__3(
        v___f_4128_,
        v_s_4129_,
        v_x_4130_,
        v_t_4131_,
    );
    leanh::lean_dec_ref(v_t_4131_);
    leanh::lean_dec(v_x_4130_);
    return v_res_4132_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(
    mut v_x_4133_: *mut leanh::LeanObject,
    mut v_x_4134_: *mut leanh::LeanObject,
    mut v_x_4135_: *mut leanh::LeanObject,
    mut v_x_4136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: u8 = 0;
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: u8 = 0;
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4137_ = leanh::lean_ctor_get(v_x_4133_, 0);
                v_vs_4138_ = leanh::lean_ctor_get(v_x_4133_, 1);
                v_isSharedCheck_4162_ = (!leanh::lean_is_exclusive(v_x_4133_)) as u8;
                if v_isSharedCheck_4162_ == 0 {
                    v___x_4140_ = v_x_4133_;
                    v_isShared_4141_ = v_isSharedCheck_4162_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4138_);
                    leanh::lean_inc(v_ks_4137_);
                    leanh::lean_dec(v_x_4133_);
                    v___x_4140_ = leanh::lean_box(0);
                    v_isShared_4141_ = v_isSharedCheck_4162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4142_ = lean_array_get_size(v_ks_4137_);
                v___x_4143_ = lean_nat_dec_lt(v_x_4134_, v___x_4142_);
                if v___x_4143_ == 0 {
                    leanh::lean_dec(v_x_4134_);
                    v___x_4144_ = lean_array_push(v_ks_4137_, v_x_4135_);
                    v___x_4145_ = lean_array_push(v_vs_4138_, v_x_4136_);
                    if v_isShared_4141_ == 0 {
                        leanh::lean_ctor_set(v___x_4140_, 1, v___x_4145_);
                        leanh::lean_ctor_set(v___x_4140_, 0, v___x_4144_);
                        v___x_4147_ = v___x_4140_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4148_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4144_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4148_, 1, v___x_4145_);
                        v___x_4147_ = v_reuseFailAlloc_4148_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4149_ = lean_array_fget_borrowed(v_ks_4137_, v_x_4134_);
                    leanh::lean_inc(v_k_x27_4149_);
                    leanh::lean_inc_ref(v_x_4135_);
                    v___x_4150_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_x_4135_,
                        v_k_x27_4149_,
                    );
                    if v___x_4150_ == 0 {
                        if v_isShared_4141_ == 0 {
                            v___x_4152_ = v___x_4140_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4156_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_ks_4137_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 1, v_vs_4138_);
                            v___x_4152_ = v_reuseFailAlloc_4156_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4157_ = lean_array_fset(v_ks_4137_, v_x_4134_, v_x_4135_);
                        v___x_4158_ = lean_array_fset(v_vs_4138_, v_x_4134_, v_x_4136_);
                        leanh::lean_dec(v_x_4134_);
                        if v_isShared_4141_ == 0 {
                            leanh::lean_ctor_set(v___x_4140_, 1, v___x_4158_);
                            leanh::lean_ctor_set(v___x_4140_, 0, v___x_4157_);
                            v___x_4160_ = v___x_4140_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4161_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4157_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 1, v___x_4158_);
                            v___x_4160_ = v_reuseFailAlloc_4161_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4147_;
            }
            3 => {
                v___x_4153_ = leanh::lean_unsigned_to_nat(1);
                v___x_4154_ = lean_nat_add(v_x_4134_, v___x_4153_);
                leanh::lean_dec(v_x_4134_);
                v_x_4133_ = v___x_4152_;
                v_x_4134_ = v___x_4154_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(
    mut v_n_4163_: *mut leanh::LeanObject,
    mut v_k_4164_: *mut leanh::LeanObject,
    mut v_v_4165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = leanh::lean_unsigned_to_nat(0);
    v___x_4167_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(v_n_4163_, v___x_4166_, v_k_4164_, v_v_4165_);
    return v___x_4167_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: u64 = 0;
    v___x_4168_ = leanh::lean_unsigned_to_nat(1723);
    v___x_4169_ = lean_uint64_of_nat(v___x_4168_);
    return v___x_4169_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_4170_: usize = 0;
    let mut v___x_4171_: usize = 0;
    let mut v___x_4172_: usize = 0;
    v___x_4170_ = 5usize;
    v___x_4171_ = 1usize;
    v___x_4172_ = lean_usize_shift_left(v___x_4171_, v___x_4170_);
    return v___x_4172_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_4173_: usize = 0;
    let mut v___x_4174_: usize = 0;
    let mut v___x_4175_: usize = 0;
    v___x_4173_ = 1usize;
    v___x_4174_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__0);
    v___x_4175_ = lean_usize_sub(v___x_4174_, v___x_4173_);
    return v___x_4175_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4176_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(
    mut v_x_4177_: *mut leanh::LeanObject,
    mut v_x_4178_: usize,
    mut v_x_4179_: usize,
    mut v_x_4180_: *mut leanh::LeanObject,
    mut v_x_4181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: usize = 0;
    let mut v___x_4184_: usize = 0;
    let mut v___x_4185_: usize = 0;
    let mut v___x_4186_: usize = 0;
    let mut v_j_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: u8 = 0;
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v_v_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4207_: u8 = 0;
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v_node_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4217_: u8 = 0;
    let mut v___x_4218_: usize = 0;
    let mut v___x_4219_: usize = 0;
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4226_: u8 = 0;
    let mut v_unused_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4237_: u8 = 0;
    let mut v_ks_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: usize = 0;
    let mut v___x_4244_: u8 = 0;
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v_reuseFailAlloc_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4249_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4177_) == 0 {
                    v_es_4182_ = leanh::lean_ctor_get(v_x_4177_, 0);
                    v___x_4183_ = 5usize;
                    v___x_4184_ = 1usize;
                    v___x_4185_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
                    v___x_4186_ = lean_usize_land(v_x_4178_, v___x_4185_);
                    v_j_4187_ = lean_usize_to_nat(v___x_4186_);
                    v___x_4188_ = lean_array_get_size(v_es_4182_);
                    v___x_4189_ = lean_nat_dec_lt(v_j_4187_, v___x_4188_);
                    if v___x_4189_ == 0 {
                        leanh::lean_dec(v_j_4187_);
                        leanh::lean_dec(v_x_4181_);
                        leanh::lean_dec_ref(v_x_4180_);
                        return v_x_4177_;
                    } else {
                        leanh::lean_inc_ref(v_es_4182_);
                        v_isSharedCheck_4226_ = (!leanh::lean_is_exclusive(v_x_4177_)) as u8;
                        if v_isSharedCheck_4226_ == 0 {
                            v_unused_4227_ = leanh::lean_ctor_get(v_x_4177_, 0);
                            leanh::lean_dec(v_unused_4227_);
                            v___x_4191_ = v_x_4177_;
                            v_isShared_4192_ = v_isSharedCheck_4226_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4177_);
                            v___x_4191_ = leanh::lean_box(0);
                            v_isShared_4192_ = v_isSharedCheck_4226_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4228_ = leanh::lean_ctor_get(v_x_4177_, 0);
                    v_vs_4229_ = leanh::lean_ctor_get(v_x_4177_, 1);
                    v_isSharedCheck_4249_ = (!leanh::lean_is_exclusive(v_x_4177_)) as u8;
                    if v_isSharedCheck_4249_ == 0 {
                        v___x_4231_ = v_x_4177_;
                        v_isShared_4232_ = v_isSharedCheck_4249_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4229_);
                        leanh::lean_inc(v_ks_4228_);
                        leanh::lean_dec(v_x_4177_);
                        v___x_4231_ = leanh::lean_box(0);
                        v_isShared_4232_ = v_isSharedCheck_4249_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4193_ = lean_array_fget(v_es_4182_, v_j_4187_);
                v___x_4194_ = leanh::lean_box(0);
                v_xs_x27_4195_ = lean_array_fset(v_es_4182_, v_j_4187_, v___x_4194_);
                match leanh::lean_obj_tag(v_v_4193_) {
                    0 => {
                        v_key_4202_ = leanh::lean_ctor_get(v_v_4193_, 0);
                        v_val_4203_ = leanh::lean_ctor_get(v_v_4193_, 1);
                        v_isSharedCheck_4213_ = (!leanh::lean_is_exclusive(v_v_4193_)) as u8;
                        if v_isSharedCheck_4213_ == 0 {
                            v___x_4205_ = v_v_4193_;
                            v_isShared_4206_ = v_isSharedCheck_4213_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4203_);
                            leanh::lean_inc(v_key_4202_);
                            leanh::lean_dec(v_v_4193_);
                            v___x_4205_ = leanh::lean_box(0);
                            v_isShared_4206_ = v_isSharedCheck_4213_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4214_ = leanh::lean_ctor_get(v_v_4193_, 0);
                        v_isSharedCheck_4224_ = (!leanh::lean_is_exclusive(v_v_4193_)) as u8;
                        if v_isSharedCheck_4224_ == 0 {
                            v___x_4216_ = v_v_4193_;
                            v_isShared_4217_ = v_isSharedCheck_4224_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4214_);
                            leanh::lean_dec(v_v_4193_);
                            v___x_4216_ = leanh::lean_box(0);
                            v_isShared_4217_ = v_isSharedCheck_4224_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4225_, 0, v_x_4180_);
                        leanh::lean_ctor_set(v___x_4225_, 1, v_x_4181_);
                        v___y_4197_ = v___x_4225_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4198_ = lean_array_fset(v_xs_x27_4195_, v_j_4187_, v___y_4197_);
                leanh::lean_dec(v_j_4187_);
                if v_isShared_4192_ == 0 {
                    leanh::lean_ctor_set(v___x_4191_, 0, v___x_4198_);
                    v___x_4200_ = v___x_4191_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4198_);
                    v___x_4200_ = v_reuseFailAlloc_4201_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4200_;
            }
            4 => {
                leanh::lean_inc(v_key_4202_);
                leanh::lean_inc_ref(v_x_4180_);
                v___x_4207_ =
                    l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(v_x_4180_, v_key_4202_);
                if v___x_4207_ == 0 {
                    leanh::lean_del_object(v___x_4205_);
                    v___x_4208_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4202_,
                        v_val_4203_,
                        v_x_4180_,
                        v_x_4181_,
                    );
                    v___x_4209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4209_, 0, v___x_4208_);
                    v___y_4197_ = v___x_4209_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4203_);
                    leanh::lean_dec(v_key_4202_);
                    if v_isShared_4206_ == 0 {
                        leanh::lean_ctor_set(v___x_4205_, 1, v_x_4181_);
                        leanh::lean_ctor_set(v___x_4205_, 0, v_x_4180_);
                        v___x_4211_ = v___x_4205_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4212_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_x_4180_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4212_, 1, v_x_4181_);
                        v___x_4211_ = v_reuseFailAlloc_4212_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4197_ = v___x_4211_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4218_ = lean_usize_shift_right(v_x_4178_, v___x_4183_);
                v___x_4219_ = lean_usize_add(v_x_4179_, v___x_4184_);
                v___x_4220_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_node_4214_, v___x_4218_, v___x_4219_, v_x_4180_, v_x_4181_);
                if v_isShared_4217_ == 0 {
                    leanh::lean_ctor_set(v___x_4216_, 0, v___x_4220_);
                    v___x_4222_ = v___x_4216_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
                    v___x_4222_ = v_reuseFailAlloc_4223_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4197_ = v___x_4222_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4232_ == 0 {
                    v___x_4234_ = v___x_4231_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4248_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_ks_4228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 1, v_vs_4229_);
                    v___x_4234_ = v_reuseFailAlloc_4248_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4235_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v___x_4234_, v_x_4180_, v_x_4181_);
                v___x_4243_ = 7usize;
                v___x_4244_ = lean_usize_dec_le(v___x_4243_, v_x_4179_);
                if v___x_4244_ == 0 {
                    v___x_4245_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4235_);
                    v___x_4246_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4247_ = lean_nat_dec_lt(v___x_4245_, v___x_4246_);
                    leanh::lean_dec(v___x_4245_);
                    v___y_4237_ = v___x_4247_;
                    state = 10;
                    continue;
                } else {
                    v___y_4237_ = v___x_4244_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4237_ == 0 {
                    v_ks_4238_ = leanh::lean_ctor_get(v_newNode_4235_, 0);
                    leanh::lean_inc_ref(v_ks_4238_);
                    v_vs_4239_ = leanh::lean_ctor_get(v_newNode_4235_, 1);
                    leanh::lean_inc_ref(v_vs_4239_);
                    leanh::lean_dec_ref(v_newNode_4235_);
                    v___x_4240_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4241_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__2);
                    v___x_4242_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_x_4179_, v_ks_4238_, v_vs_4239_, v___x_4240_, v___x_4241_);
                    leanh::lean_dec_ref(v_vs_4239_);
                    leanh::lean_dec_ref(v_ks_4238_);
                    return v___x_4242_;
                } else {
                    return v_newNode_4235_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(
    mut v_depth_4250_: usize,
    mut v_keys_4251_: *mut leanh::LeanObject,
    mut v_vals_4252_: *mut leanh::LeanObject,
    mut v_i_4253_: *mut leanh::LeanObject,
    mut v_entries_4254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: u8 = 0;
    let mut v_k_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4260_: u64 = 0;
    let mut v_h_4261_: usize = 0;
    let mut v___x_4262_: usize = 0;
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: usize = 0;
    let mut v___x_4265_: usize = 0;
    let mut v___x_4266_: usize = 0;
    let mut v_h_4267_: usize = 0;
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: u64 = 0;
    let mut v_hash_4273_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4255_ = lean_array_get_size(v_keys_4251_);
                v___x_4256_ = lean_nat_dec_lt(v_i_4253_, v___x_4255_);
                if v___x_4256_ == 0 {
                    leanh::lean_dec(v_i_4253_);
                    return v_entries_4254_;
                } else {
                    v_k_4257_ = lean_array_fget_borrowed(v_keys_4251_, v_i_4253_);
                    v_v_4258_ = lean_array_fget_borrowed(v_vals_4252_, v_i_4253_);
                    v___x_4271_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_k_4257_);
                    if leanh::lean_obj_tag(v___x_4271_) == 0 {
                        v___x_4272_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_4260_ = v___x_4272_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4273_ = leanh::lean_ctor_get_uint64(
                            v___x_4271_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        leanh::lean_dec(v___x_4271_);
                        v___y_4260_ = v_hash_4273_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4261_ = lean_uint64_to_usize(v___y_4260_);
                v___x_4262_ = 5usize;
                v___x_4263_ = leanh::lean_unsigned_to_nat(1);
                v___x_4264_ = 1usize;
                v___x_4265_ = lean_usize_sub(v_depth_4250_, v___x_4264_);
                v___x_4266_ = lean_usize_mul(v___x_4262_, v___x_4265_);
                v_h_4267_ = lean_usize_shift_right(v_h_4261_, v___x_4266_);
                v___x_4268_ = lean_nat_add(v_i_4253_, v___x_4263_);
                leanh::lean_dec(v_i_4253_);
                leanh::lean_inc(v_v_4258_);
                leanh::lean_inc(v_k_4257_);
                v___x_4269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_entries_4254_, v_h_4267_, v_depth_4250_, v_k_4257_, v_v_4258_);
                v_i_4253_ = v___x_4268_;
                v_entries_4254_ = v___x_4269_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_4274_: *mut leanh::LeanObject,
    mut v_keys_4275_: *mut leanh::LeanObject,
    mut v_vals_4276_: *mut leanh::LeanObject,
    mut v_i_4277_: *mut leanh::LeanObject,
    mut v_entries_4278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4279_: usize = 0;
    let mut v_res_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4279_ = leanh::lean_unbox_usize(v_depth_4274_);
    leanh::lean_dec(v_depth_4274_);
    v_res_4280_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4279_, v_keys_4275_, v_vals_4276_, v_i_4277_, v_entries_4278_);
    leanh::lean_dec_ref(v_vals_4276_);
    leanh::lean_dec_ref(v_keys_4275_);
    return v_res_4280_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___boxed(
    mut v_x_4281_: *mut leanh::LeanObject,
    mut v_x_4282_: *mut leanh::LeanObject,
    mut v_x_4283_: *mut leanh::LeanObject,
    mut v_x_4284_: *mut leanh::LeanObject,
    mut v_x_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26567__boxed_4286_: usize = 0;
    let mut v_x_26568__boxed_4287_: usize = 0;
    let mut v_res_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26567__boxed_4286_ = leanh::lean_unbox_usize(v_x_4282_);
    leanh::lean_dec(v_x_4282_);
    v_x_26568__boxed_4287_ = leanh::lean_unbox_usize(v_x_4283_);
    leanh::lean_dec(v_x_4283_);
    v_res_4288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_4281_, v_x_26567__boxed_4286_, v_x_26568__boxed_4287_, v_x_4284_, v_x_4285_);
    return v_res_4288_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(
    mut v_x_4289_: *mut leanh::LeanObject,
    mut v_x_4290_: *mut leanh::LeanObject,
    mut v_x_4291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4293_: u64 = 0;
    let mut v___x_4294_: usize = 0;
    let mut v___x_4295_: usize = 0;
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u64 = 0;
    let mut v_hash_4299_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4297_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_4290_);
                if leanh::lean_obj_tag(v___x_4297_) == 0 {
                    v___x_4298_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4293_ = v___x_4298_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4299_ = leanh::lean_ctor_get_uint64(
                        v___x_4297_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___x_4297_);
                    v___y_4293_ = v_hash_4299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4294_ = lean_uint64_to_usize(v___y_4293_);
                v___x_4295_ = 1usize;
                v___x_4296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_4289_, v___x_4294_, v___x_4295_, v_x_4290_, v_x_4291_);
                return v___x_4296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___lam__4(
    mut v_d_4300_: *mut leanh::LeanObject,
    mut v_a_4301_: *mut leanh::LeanObject,
    mut v_x_4302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4303_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_ofOrigin(v_a_4301_);
    if leanh::lean_obj_tag(v___x_4303_) == 0 {
        return v_d_4300_;
    } else {
        let mut v_val_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4304_ = leanh::lean_ctor_get(v___x_4303_, 0);
        leanh::lean_inc(v_val_4304_);
        leanh::lean_dec_ref_known(v___x_4303_, 1);
        v___x_4305_ = leanh::lean_box(0);
        v___x_4306_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(v_d_4300_, v_val_4304_, v___x_4305_);
        return v___x_4306_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34___redArg(
    mut v_x_4307_: *mut leanh::LeanObject,
    mut v_x_4308_: *mut leanh::LeanObject,
    mut v_x_4309_: *mut leanh::LeanObject,
    mut v_x_4310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4311_ = leanh::lean_ctor_get(v_x_4307_, 0);
                v_vs_4312_ = leanh::lean_ctor_get(v_x_4307_, 1);
                v_isSharedCheck_4336_ = (!leanh::lean_is_exclusive(v_x_4307_)) as u8;
                if v_isSharedCheck_4336_ == 0 {
                    v___x_4314_ = v_x_4307_;
                    v_isShared_4315_ = v_isSharedCheck_4336_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4312_);
                    leanh::lean_inc(v_ks_4311_);
                    leanh::lean_dec(v_x_4307_);
                    v___x_4314_ = leanh::lean_box(0);
                    v_isShared_4315_ = v_isSharedCheck_4336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4316_ = lean_array_get_size(v_ks_4311_);
                v___x_4317_ = lean_nat_dec_lt(v_x_4308_, v___x_4316_);
                if v___x_4317_ == 0 {
                    leanh::lean_dec(v_x_4308_);
                    v___x_4318_ = lean_array_push(v_ks_4311_, v_x_4309_);
                    v___x_4319_ = lean_array_push(v_vs_4312_, v_x_4310_);
                    if v_isShared_4315_ == 0 {
                        leanh::lean_ctor_set(v___x_4314_, 1, v___x_4319_);
                        leanh::lean_ctor_set(v___x_4314_, 0, v___x_4318_);
                        v___x_4321_ = v___x_4314_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4322_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4318_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 1, v___x_4319_);
                        v___x_4321_ = v_reuseFailAlloc_4322_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4323_ = lean_array_fget_borrowed(v_ks_4311_, v_x_4308_);
                    v___x_4324_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4309_, v_k_x27_4323_);
                    if v___x_4324_ == 0 {
                        if v_isShared_4315_ == 0 {
                            v___x_4326_ = v___x_4314_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4330_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_ks_4311_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4330_, 1, v_vs_4312_);
                            v___x_4326_ = v_reuseFailAlloc_4330_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4331_ = lean_array_fset(v_ks_4311_, v_x_4308_, v_x_4309_);
                        v___x_4332_ = lean_array_fset(v_vs_4312_, v_x_4308_, v_x_4310_);
                        leanh::lean_dec(v_x_4308_);
                        if v_isShared_4315_ == 0 {
                            leanh::lean_ctor_set(v___x_4314_, 1, v___x_4332_);
                            leanh::lean_ctor_set(v___x_4314_, 0, v___x_4331_);
                            v___x_4334_ = v___x_4314_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4335_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4331_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 1, v___x_4332_);
                            v___x_4334_ = v_reuseFailAlloc_4335_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4321_;
            }
            3 => {
                v___x_4327_ = leanh::lean_unsigned_to_nat(1);
                v___x_4328_ = lean_nat_add(v_x_4308_, v___x_4327_);
                leanh::lean_dec(v_x_4308_);
                v_x_4307_ = v___x_4326_;
                v_x_4308_ = v___x_4328_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28___redArg(
    mut v_n_4337_: *mut leanh::LeanObject,
    mut v_k_4338_: *mut leanh::LeanObject,
    mut v_v_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4340_ = leanh::lean_unsigned_to_nat(0);
    v___x_4341_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34___redArg(v_n_4337_, v___x_4340_, v_k_4338_, v_v_4339_);
    return v___x_4341_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4342_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4342_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(
    mut v_x_4343_: *mut leanh::LeanObject,
    mut v_x_4344_: usize,
    mut v_x_4345_: usize,
    mut v_x_4346_: *mut leanh::LeanObject,
    mut v_x_4347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: usize = 0;
    let mut v___x_4350_: usize = 0;
    let mut v___x_4351_: usize = 0;
    let mut v___x_4352_: usize = 0;
    let mut v_j_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: u8 = 0;
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v_v_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4372_: u8 = 0;
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4379_: u8 = 0;
    let mut v_node_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4383_: u8 = 0;
    let mut v___x_4384_: usize = 0;
    let mut v___x_4385_: usize = 0;
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut v_unused_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4403_: u8 = 0;
    let mut v_ks_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: usize = 0;
    let mut v___x_4410_: u8 = 0;
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: u8 = 0;
    let mut v_reuseFailAlloc_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4343_) == 0 {
                    v_es_4348_ = leanh::lean_ctor_get(v_x_4343_, 0);
                    v___x_4349_ = 5usize;
                    v___x_4350_ = 1usize;
                    v___x_4351_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
                    v___x_4352_ = lean_usize_land(v_x_4344_, v___x_4351_);
                    v_j_4353_ = lean_usize_to_nat(v___x_4352_);
                    v___x_4354_ = lean_array_get_size(v_es_4348_);
                    v___x_4355_ = lean_nat_dec_lt(v_j_4353_, v___x_4354_);
                    if v___x_4355_ == 0 {
                        leanh::lean_dec(v_j_4353_);
                        leanh::lean_dec(v_x_4347_);
                        leanh::lean_dec(v_x_4346_);
                        return v_x_4343_;
                    } else {
                        leanh::lean_inc_ref(v_es_4348_);
                        v_isSharedCheck_4392_ = (!leanh::lean_is_exclusive(v_x_4343_)) as u8;
                        if v_isSharedCheck_4392_ == 0 {
                            v_unused_4393_ = leanh::lean_ctor_get(v_x_4343_, 0);
                            leanh::lean_dec(v_unused_4393_);
                            v___x_4357_ = v_x_4343_;
                            v_isShared_4358_ = v_isSharedCheck_4392_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4343_);
                            v___x_4357_ = leanh::lean_box(0);
                            v_isShared_4358_ = v_isSharedCheck_4392_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4394_ = leanh::lean_ctor_get(v_x_4343_, 0);
                    v_vs_4395_ = leanh::lean_ctor_get(v_x_4343_, 1);
                    v_isSharedCheck_4415_ = (!leanh::lean_is_exclusive(v_x_4343_)) as u8;
                    if v_isSharedCheck_4415_ == 0 {
                        v___x_4397_ = v_x_4343_;
                        v_isShared_4398_ = v_isSharedCheck_4415_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4395_);
                        leanh::lean_inc(v_ks_4394_);
                        leanh::lean_dec(v_x_4343_);
                        v___x_4397_ = leanh::lean_box(0);
                        v_isShared_4398_ = v_isSharedCheck_4415_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4359_ = lean_array_fget(v_es_4348_, v_j_4353_);
                v___x_4360_ = leanh::lean_box(0);
                v_xs_x27_4361_ = lean_array_fset(v_es_4348_, v_j_4353_, v___x_4360_);
                match leanh::lean_obj_tag(v_v_4359_) {
                    0 => {
                        v_key_4368_ = leanh::lean_ctor_get(v_v_4359_, 0);
                        v_val_4369_ = leanh::lean_ctor_get(v_v_4359_, 1);
                        v_isSharedCheck_4379_ = (!leanh::lean_is_exclusive(v_v_4359_)) as u8;
                        if v_isSharedCheck_4379_ == 0 {
                            v___x_4371_ = v_v_4359_;
                            v_isShared_4372_ = v_isSharedCheck_4379_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4369_);
                            leanh::lean_inc(v_key_4368_);
                            leanh::lean_dec(v_v_4359_);
                            v___x_4371_ = leanh::lean_box(0);
                            v_isShared_4372_ = v_isSharedCheck_4379_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4380_ = leanh::lean_ctor_get(v_v_4359_, 0);
                        v_isSharedCheck_4390_ = (!leanh::lean_is_exclusive(v_v_4359_)) as u8;
                        if v_isSharedCheck_4390_ == 0 {
                            v___x_4382_ = v_v_4359_;
                            v_isShared_4383_ = v_isSharedCheck_4390_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4380_);
                            leanh::lean_dec(v_v_4359_);
                            v___x_4382_ = leanh::lean_box(0);
                            v_isShared_4383_ = v_isSharedCheck_4390_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4391_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4391_, 0, v_x_4346_);
                        leanh::lean_ctor_set(v___x_4391_, 1, v_x_4347_);
                        v___y_4363_ = v___x_4391_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4364_ = lean_array_fset(v_xs_x27_4361_, v_j_4353_, v___y_4363_);
                leanh::lean_dec(v_j_4353_);
                if v_isShared_4358_ == 0 {
                    leanh::lean_ctor_set(v___x_4357_, 0, v___x_4364_);
                    v___x_4366_ = v___x_4357_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4367_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4364_);
                    v___x_4366_ = v_reuseFailAlloc_4367_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4366_;
            }
            4 => {
                v___x_4373_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4346_, v_key_4368_);
                if v___x_4373_ == 0 {
                    leanh::lean_del_object(v___x_4371_);
                    v___x_4374_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4368_,
                        v_val_4369_,
                        v_x_4346_,
                        v_x_4347_,
                    );
                    v___x_4375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4375_, 0, v___x_4374_);
                    v___y_4363_ = v___x_4375_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4369_);
                    leanh::lean_dec(v_key_4368_);
                    if v_isShared_4372_ == 0 {
                        leanh::lean_ctor_set(v___x_4371_, 1, v_x_4347_);
                        leanh::lean_ctor_set(v___x_4371_, 0, v_x_4346_);
                        v___x_4377_ = v___x_4371_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4378_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_x_4346_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4378_, 1, v_x_4347_);
                        v___x_4377_ = v_reuseFailAlloc_4378_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4363_ = v___x_4377_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4384_ = lean_usize_shift_right(v_x_4344_, v___x_4349_);
                v___x_4385_ = lean_usize_add(v_x_4345_, v___x_4350_);
                v___x_4386_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_node_4380_, v___x_4384_, v___x_4385_, v_x_4346_, v_x_4347_);
                if v_isShared_4383_ == 0 {
                    leanh::lean_ctor_set(v___x_4382_, 0, v___x_4386_);
                    v___x_4388_ = v___x_4382_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4363_ = v___x_4388_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4398_ == 0 {
                    v___x_4400_ = v___x_4397_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_ks_4394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_vs_4395_);
                    v___x_4400_ = v_reuseFailAlloc_4414_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4401_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28___redArg(v___x_4400_, v_x_4346_, v_x_4347_);
                v___x_4409_ = 7usize;
                v___x_4410_ = lean_usize_dec_le(v___x_4409_, v_x_4345_);
                if v___x_4410_ == 0 {
                    v___x_4411_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4401_);
                    v___x_4412_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4413_ = lean_nat_dec_lt(v___x_4411_, v___x_4412_);
                    leanh::lean_dec(v___x_4411_);
                    v___y_4403_ = v___x_4413_;
                    state = 10;
                    continue;
                } else {
                    v___y_4403_ = v___x_4410_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4403_ == 0 {
                    v_ks_4404_ = leanh::lean_ctor_get(v_newNode_4401_, 0);
                    leanh::lean_inc_ref(v_ks_4404_);
                    v_vs_4405_ = leanh::lean_ctor_get(v_newNode_4401_, 1);
                    leanh::lean_inc_ref(v_vs_4405_);
                    leanh::lean_dec_ref(v_newNode_4401_);
                    v___x_4406_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4407_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___closed__0);
                    v___x_4408_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(v_x_4345_, v_ks_4404_, v_vs_4405_, v___x_4406_, v___x_4407_);
                    leanh::lean_dec_ref(v_vs_4405_);
                    leanh::lean_dec_ref(v_ks_4404_);
                    return v___x_4408_;
                } else {
                    return v_newNode_4401_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(
    mut v_depth_4416_: usize,
    mut v_keys_4417_: *mut leanh::LeanObject,
    mut v_vals_4418_: *mut leanh::LeanObject,
    mut v_i_4419_: *mut leanh::LeanObject,
    mut v_entries_4420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: u8 = 0;
    let mut v_k_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: u64 = 0;
    let mut v_h_4426_: usize = 0;
    let mut v___x_4427_: usize = 0;
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: usize = 0;
    let mut v___x_4430_: usize = 0;
    let mut v___x_4431_: usize = 0;
    let mut v_h_4432_: usize = 0;
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4421_ = lean_array_get_size(v_keys_4417_);
                v___x_4422_ = lean_nat_dec_lt(v_i_4419_, v___x_4421_);
                if v___x_4422_ == 0 {
                    leanh::lean_dec(v_i_4419_);
                    return v_entries_4420_;
                } else {
                    v_k_4423_ = lean_array_fget_borrowed(v_keys_4417_, v_i_4419_);
                    v_v_4424_ = lean_array_fget_borrowed(v_vals_4418_, v_i_4419_);
                    v___x_4425_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_4423_);
                    v_h_4426_ = lean_uint64_to_usize(v___x_4425_);
                    v___x_4427_ = 5usize;
                    v___x_4428_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4429_ = 1usize;
                    v___x_4430_ = lean_usize_sub(v_depth_4416_, v___x_4429_);
                    v___x_4431_ = lean_usize_mul(v___x_4427_, v___x_4430_);
                    v_h_4432_ = lean_usize_shift_right(v_h_4426_, v___x_4431_);
                    v___x_4433_ = lean_nat_add(v_i_4419_, v___x_4428_);
                    leanh::lean_dec(v_i_4419_);
                    leanh::lean_inc(v_v_4424_);
                    leanh::lean_inc(v_k_4423_);
                    v___x_4434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_entries_4420_, v_h_4432_, v_depth_4416_, v_k_4423_, v_v_4424_);
                    v_i_4419_ = v___x_4433_;
                    v_entries_4420_ = v___x_4434_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg___boxed(
    mut v_depth_4436_: *mut leanh::LeanObject,
    mut v_keys_4437_: *mut leanh::LeanObject,
    mut v_vals_4438_: *mut leanh::LeanObject,
    mut v_i_4439_: *mut leanh::LeanObject,
    mut v_entries_4440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4441_: usize = 0;
    let mut v_res_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4441_ = leanh::lean_unbox_usize(v_depth_4436_);
    leanh::lean_dec(v_depth_4436_);
    v_res_4442_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(v_depth_boxed_4441_, v_keys_4437_, v_vals_4438_, v_i_4439_, v_entries_4440_);
    leanh::lean_dec_ref(v_vals_4438_);
    leanh::lean_dec_ref(v_keys_4437_);
    return v_res_4442_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg___boxed(
    mut v_x_4443_: *mut leanh::LeanObject,
    mut v_x_4444_: *mut leanh::LeanObject,
    mut v_x_4445_: *mut leanh::LeanObject,
    mut v_x_4446_: *mut leanh::LeanObject,
    mut v_x_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26849__boxed_4448_: usize = 0;
    let mut v_x_26850__boxed_4449_: usize = 0;
    let mut v_res_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26849__boxed_4448_ = leanh::lean_unbox_usize(v_x_4444_);
    leanh::lean_dec(v_x_4444_);
    v_x_26850__boxed_4449_ = leanh::lean_unbox_usize(v_x_4445_);
    leanh::lean_dec(v_x_4445_);
    v_res_4450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_x_4443_, v_x_26849__boxed_4448_, v_x_26850__boxed_4449_, v_x_4446_, v_x_4447_);
    return v_res_4450_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(
    mut v_x_4451_: *mut leanh::LeanObject,
    mut v_x_4452_: *mut leanh::LeanObject,
    mut v_x_4453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4454_: u64 = 0;
    let mut v___x_4455_: usize = 0;
    let mut v___x_4456_: usize = 0;
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4454_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4452_);
    v___x_4455_ = lean_uint64_to_usize(v___x_4454_);
    v___x_4456_ = 1usize;
    v___x_4457_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_x_4451_, v___x_4455_, v___x_4456_, v_x_4452_, v_x_4453_);
    return v___x_4457_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(
    mut v_keys_4458_: *mut leanh::LeanObject,
    mut v_vals_4459_: *mut leanh::LeanObject,
    mut v_i_4460_: *mut leanh::LeanObject,
    mut v_k_4461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: u8 = 0;
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4462_ = lean_array_get_size(v_keys_4458_);
                v___x_4463_ = lean_nat_dec_lt(v_i_4460_, v___x_4462_);
                if v___x_4463_ == 0 {
                    leanh::lean_dec(v_i_4460_);
                    v___x_4464_ = leanh::lean_box(0);
                    return v___x_4464_;
                } else {
                    v_k_x27_4465_ = lean_array_fget_borrowed(v_keys_4458_, v_i_4460_);
                    v___x_4466_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_4461_, v_k_x27_4465_);
                    if v___x_4466_ == 0 {
                        v___x_4467_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4468_ = lean_nat_add(v_i_4460_, v___x_4467_);
                        leanh::lean_dec(v_i_4460_);
                        v_i_4460_ = v___x_4468_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4470_ = lean_array_fget_borrowed(v_vals_4459_, v_i_4460_);
                        leanh::lean_dec(v_i_4460_);
                        leanh::lean_inc(v___x_4470_);
                        v___x_4471_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4471_, 0, v___x_4470_);
                        return v___x_4471_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg___boxed(
    mut v_keys_4472_: *mut leanh::LeanObject,
    mut v_vals_4473_: *mut leanh::LeanObject,
    mut v_i_4474_: *mut leanh::LeanObject,
    mut v_k_4475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(v_keys_4472_, v_vals_4473_, v_i_4474_, v_k_4475_);
    leanh::lean_dec(v_k_4475_);
    leanh::lean_dec_ref(v_vals_4473_);
    leanh::lean_dec_ref(v_keys_4472_);
    return v_res_4476_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(
    mut v_x_4477_: *mut leanh::LeanObject,
    mut v_x_4478_: usize,
    mut v_x_4479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: usize = 0;
    let mut v___x_4483_: usize = 0;
    let mut v___x_4484_: usize = 0;
    let mut v_j_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: u8 = 0;
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: usize = 0;
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4477_) == 0 {
                    v_es_4480_ = leanh::lean_ctor_get(v_x_4477_, 0);
                    v___x_4481_ = leanh::lean_box(2);
                    v___x_4482_ = 5usize;
                    v___x_4483_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
                    v___x_4484_ = lean_usize_land(v_x_4478_, v___x_4483_);
                    v_j_4485_ = lean_usize_to_nat(v___x_4484_);
                    v___x_4486_ = lean_array_get_borrowed(v___x_4481_, v_es_4480_, v_j_4485_);
                    leanh::lean_dec(v_j_4485_);
                    match leanh::lean_obj_tag(v___x_4486_) {
                        0 => {
                            v_key_4487_ = leanh::lean_ctor_get(v___x_4486_, 0);
                            v_val_4488_ = leanh::lean_ctor_get(v___x_4486_, 1);
                            v___x_4489_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4479_, v_key_4487_);
                            if v___x_4489_ == 0 {
                                v___x_4490_ = leanh::lean_box(0);
                                return v___x_4490_;
                            } else {
                                leanh::lean_inc(v_val_4488_);
                                v___x_4491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4491_, 0, v_val_4488_);
                                return v___x_4491_;
                            }
                        }
                        1 => {
                            v_node_4492_ = leanh::lean_ctor_get(v___x_4486_, 0);
                            v___x_4493_ = lean_usize_shift_right(v_x_4478_, v___x_4482_);
                            v_x_4477_ = v_node_4492_;
                            v_x_4478_ = v___x_4493_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4495_ = leanh::lean_box(0);
                            return v___x_4495_;
                        }
                    }
                } else {
                    v_ks_4496_ = leanh::lean_ctor_get(v_x_4477_, 0);
                    v_vs_4497_ = leanh::lean_ctor_get(v_x_4477_, 1);
                    v___x_4498_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4499_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(v_ks_4496_, v_vs_4497_, v___x_4498_, v_x_4479_);
                    return v___x_4499_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg___boxed(
    mut v_x_4500_: *mut leanh::LeanObject,
    mut v_x_4501_: *mut leanh::LeanObject,
    mut v_x_4502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_27043__boxed_4503_: usize = 0;
    let mut v_res_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_27043__boxed_4503_ = leanh::lean_unbox_usize(v_x_4501_);
    leanh::lean_dec(v_x_4501_);
    v_res_4504_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(v_x_4500_, v_x_27043__boxed_4503_, v_x_4502_);
    leanh::lean_dec(v_x_4502_);
    leanh::lean_dec_ref(v_x_4500_);
    return v_res_4504_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(
    mut v_x_4505_: *mut leanh::LeanObject,
    mut v_x_4506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4507_: u64 = 0;
    let mut v___x_4508_: usize = 0;
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4507_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4506_);
    v___x_4508_ = lean_uint64_to_usize(v___x_4507_);
    v___x_4509_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(v_x_4505_, v___x_4508_, v_x_4506_);
    return v___x_4509_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_x_4510_: *mut leanh::LeanObject,
    mut v_x_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4512_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(v_x_4510_, v_x_4511_);
    leanh::lean_dec(v_x_4511_);
    leanh::lean_dec_ref(v_x_4510_);
    return v_res_4512_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4513_ = l_Lean_Meta_DiscrTree_instInhabited(leanh::lean_box(0));
    return v___x_4513_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8(
    mut v_msg_4514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4515_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8___closed__0);
    v___x_4516_ = lean_panic_fn_borrowed(v___x_4515_, v_msg_4514_);
    return v___x_4516_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21_spec__32(
    mut v_vs_4517_: *mut leanh::LeanObject,
    mut v_v_4518_: *mut leanh::LeanObject,
    mut v_i_4519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: u8 = 0;
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: u8 = 0;
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4520_ = lean_array_get_size(v_vs_4517_);
                v___x_4521_ = lean_nat_dec_lt(v_i_4519_, v___x_4520_);
                if v___x_4521_ == 0 {
                    leanh::lean_dec(v_i_4519_);
                    v___x_4522_ = lean_array_push(v_vs_4517_, v_v_4518_);
                    return v___x_4522_;
                } else {
                    v_proof_4523_ = leanh::lean_ctor_get(v_v_4518_, 1);
                    v___x_4524_ = lean_array_fget_borrowed(v_vs_4517_, v_i_4519_);
                    v_proof_4525_ = leanh::lean_ctor_get(v___x_4524_, 1);
                    leanh::lean_inc_ref(v_proof_4525_);
                    leanh::lean_inc_ref(v_proof_4523_);
                    v___x_4526_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_proof_4523_,
                        v_proof_4525_,
                    );
                    if v___x_4526_ == 0 {
                        v___x_4527_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4528_ = lean_nat_add(v_i_4519_, v___x_4527_);
                        leanh::lean_dec(v_i_4519_);
                        v_i_4519_ = v___x_4528_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4530_ = lean_array_fset(v_vs_4517_, v_i_4519_, v_v_4518_);
                        leanh::lean_dec(v_i_4519_);
                        return v___x_4530_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21(
    mut v_vs_4531_: *mut leanh::LeanObject,
    mut v_v_4532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4533_ = leanh::lean_unsigned_to_nat(0);
    v___x_4534_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21_spec__32(v_vs_4531_, v_v_4532_, v___x_4533_);
    return v___x_4534_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(
    mut v_x_4535_: *mut leanh::LeanObject,
    mut v_keys_4536_: *mut leanh::LeanObject,
    mut v_v_4537_: *mut leanh::LeanObject,
    mut v_k_4538_: *mut leanh::LeanObject,
    mut v_x_4539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4540_ = leanh::lean_unsigned_to_nat(1);
    v___x_4541_ = lean_nat_add(v_x_4535_, v___x_4540_);
    v_c_4542_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        leanh::lean_box(0),
        v_keys_4536_,
        v_v_4537_,
        v___x_4541_,
    );
    leanh::lean_dec(v___x_4541_);
    v___x_4543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4543_, 0, v_k_4538_);
    leanh::lean_ctor_set(v___x_4543_, 1, v_c_4542_);
    return v___x_4543_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0___boxed(
    mut v_x_4544_: *mut leanh::LeanObject,
    mut v_keys_4545_: *mut leanh::LeanObject,
    mut v_v_4546_: *mut leanh::LeanObject,
    mut v_k_4547_: *mut leanh::LeanObject,
    mut v_x_4548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4549_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_4544_, v_keys_4545_, v_v_4546_, v_k_4547_, v_x_4548_);
    leanh::lean_dec_ref(v_keys_4545_);
    leanh::lean_dec(v_x_4544_);
    return v_res_4549_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(
    mut v_a_4550_: *mut leanh::LeanObject,
    mut v_b_4551_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: u8 = 0;
    v_fst_4552_ = leanh::lean_ctor_get(v_a_4550_, 0);
    v_fst_4553_ = leanh::lean_ctor_get(v_b_4551_, 0);
    v___x_4554_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_4552_, v_fst_4553_);
    return v___x_4554_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1___boxed(
    mut v_a_4555_: *mut leanh::LeanObject,
    mut v_b_4556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4557_: u8 = 0;
    let mut v_r_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4557_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_a_4555_, v_b_4556_);
    leanh::lean_dec_ref(v_b_4556_);
    leanh::lean_dec_ref(v_a_4555_);
    v_r_4558_ = leanh::lean_box((v_res_4557_) as usize);
    return v_r_4558_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(
    mut v_x_4563_: *mut leanh::LeanObject,
    mut v_keys_4564_: *mut leanh::LeanObject,
    mut v_v_4565_: *mut leanh::LeanObject,
    mut v_k_4566_: *mut leanh::LeanObject,
    mut v_as_4567_: *mut leanh::LeanObject,
    mut v_k_4568_: *mut leanh::LeanObject,
    mut v_x_4569_: *mut leanh::LeanObject,
    mut v_x_4570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_midVal_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: u8 = 0;
    let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: u8 = 0;
    let mut v_snd_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4591_: u8 = 0;
    let mut v_unused_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: u8 = 0;
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4571_ = lean_nat_add(v_x_4569_, v_x_4570_);
                v___x_4572_ = leanh::lean_unsigned_to_nat(1);
                v_mid_4573_ = lean_nat_shiftr(v___x_4571_, v___x_4572_);
                leanh::lean_dec(v___x_4571_);
                v_midVal_4574_ = lean_array_fget(v_as_4567_, v_mid_4573_);
                v___x_4575_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_midVal_4574_, v_k_4568_);
                if v___x_4575_ == 0 {
                    leanh::lean_dec(v_x_4570_);
                    v___x_4576_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_k_4568_, v_midVal_4574_);
                    if v___x_4576_ == 0 {
                        leanh::lean_dec(v_x_4569_);
                        v___x_4577_ = lean_array_get_size(v_as_4567_);
                        v___x_4578_ = lean_nat_dec_lt(v_mid_4573_, v___x_4577_);
                        if v___x_4578_ == 0 {
                            leanh::lean_dec(v_midVal_4574_);
                            leanh::lean_dec(v_mid_4573_);
                            leanh::lean_dec(v_k_4566_);
                            leanh::lean_dec_ref(v_v_4565_);
                            return v_as_4567_;
                        } else {
                            v_snd_4579_ = leanh::lean_ctor_get(v_midVal_4574_, 1);
                            v_isSharedCheck_4591_ =
                                (!leanh::lean_is_exclusive(v_midVal_4574_)) as u8;
                            if v_isSharedCheck_4591_ == 0 {
                                v_unused_4592_ = leanh::lean_ctor_get(v_midVal_4574_, 0);
                                leanh::lean_dec(v_unused_4592_);
                                v___x_4581_ = v_midVal_4574_;
                                v_isShared_4582_ = v_isSharedCheck_4591_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_4579_);
                                leanh::lean_dec(v_midVal_4574_);
                                v___x_4581_ = leanh::lean_box(0);
                                v_isShared_4582_ = v_isSharedCheck_4591_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_midVal_4574_);
                        v_x_4570_ = v_mid_4573_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_midVal_4574_);
                    v___x_4594_ = lean_nat_dec_eq(v_mid_4573_, v_x_4569_);
                    if v___x_4594_ == 0 {
                        leanh::lean_dec(v_x_4569_);
                        v_x_4569_ = v_mid_4573_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_mid_4573_);
                        leanh::lean_dec(v_x_4570_);
                        v___x_4596_ = lean_nat_add(v_x_4563_, v___x_4572_);
                        v_c_4597_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(leanh::lean_box(0), v_keys_4564_, v_v_4565_, v___x_4596_);
                        leanh::lean_dec(v___x_4596_);
                        v___x_4598_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4598_, 0, v_k_4566_);
                        leanh::lean_ctor_set(v___x_4598_, 1, v_c_4597_);
                        v___x_4599_ = lean_nat_add(v_x_4569_, v___x_4572_);
                        leanh::lean_dec(v_x_4569_);
                        v_j_4600_ = lean_array_get_size(v_as_4567_);
                        v_as_4601_ = lean_array_push(v_as_4567_, v___x_4598_);
                        v___x_4602_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            leanh::lean_box(0),
                            v___x_4599_,
                            v_as_4601_,
                            v_j_4600_,
                        );
                        leanh::lean_dec(v___x_4599_);
                        return v___x_4602_;
                    }
                }
            }
            1 => {
                v___x_4583_ = leanh::lean_box(0);
                v_xs_x27_4584_ = lean_array_fset(v_as_4567_, v_mid_4573_, v___x_4583_);
                v___x_4585_ = lean_nat_add(v_x_4563_, v___x_4572_);
                v_c_4586_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_4564_, v_v_4565_, v___x_4585_, v_snd_4579_);
                leanh::lean_dec(v___x_4585_);
                if v_isShared_4582_ == 0 {
                    leanh::lean_ctor_set(v___x_4581_, 1, v_c_4586_);
                    leanh::lean_ctor_set(v___x_4581_, 0, v_k_4566_);
                    v___x_4588_ = v___x_4581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4590_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_k_4566_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4590_, 1, v_c_4586_);
                    v___x_4588_ = v_reuseFailAlloc_4590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4589_ = lean_array_fset(v_xs_x27_4584_, v_mid_4573_, v___x_4588_);
                leanh::lean_dec(v_mid_4573_);
                return v___x_4589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22(
    mut v_x_4603_: *mut leanh::LeanObject,
    mut v_keys_4604_: *mut leanh::LeanObject,
    mut v_v_4605_: *mut leanh::LeanObject,
    mut v_k_4606_: *mut leanh::LeanObject,
    mut v_as_4607_: *mut leanh::LeanObject,
    mut v_k_4608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: u8 = 0;
    v___x_4609_ = lean_array_get_size(v_as_4607_);
    v___x_4610_ = leanh::lean_unsigned_to_nat(0);
    v___x_4611_ = lean_nat_dec_eq(v___x_4609_, v___x_4610_);
    if v___x_4611_ == 0 {
        let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4613_: u8 = 0;
        v___x_4612_ = lean_array_fget_borrowed(v_as_4607_, v___x_4610_);
        v___x_4613_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_k_4608_, v___x_4612_);
        if v___x_4613_ == 0 {
            let mut v___x_4614_: u8 = 0;
            v___x_4614_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v___x_4612_, v_k_4608_);
            if v___x_4614_ == 0 {
                let mut v___x_4615_: u8 = 0;
                v___x_4615_ = lean_nat_dec_lt(v___x_4610_, v___x_4609_);
                if v___x_4615_ == 0 {
                    leanh::lean_dec(v_k_4606_);
                    leanh::lean_dec_ref(v_v_4605_);
                    return v_as_4607_;
                } else {
                    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_inc(v___x_4612_);
                    v___x_4616_ = leanh::lean_box(0);
                    v_xs_x27_4617_ = lean_array_fset(v_as_4607_, v___x_4610_, v___x_4616_);
                    v___x_4618_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(v_x_4603_, v_keys_4604_, v_v_4605_, v_k_4606_, v___x_4612_);
                    v___x_4619_ = lean_array_fset(v_xs_x27_4617_, v___x_4610_, v___x_4618_);
                    return v___x_4619_;
                }
            } else {
                let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4623_: u8 = 0;
                v___x_4620_ = leanh::lean_unsigned_to_nat(1);
                v___x_4621_ = lean_nat_sub(v___x_4609_, v___x_4620_);
                v___x_4622_ = lean_array_fget_borrowed(v_as_4607_, v___x_4621_);
                v___x_4623_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v___x_4622_, v_k_4608_);
                if v___x_4623_ == 0 {
                    let mut v___x_4624_: u8 = 0;
                    v___x_4624_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__1(v_k_4608_, v___x_4622_);
                    if v___x_4624_ == 0 {
                        let mut v___x_4625_: u8 = 0;
                        v___x_4625_ = lean_nat_dec_lt(v___x_4621_, v___x_4609_);
                        if v___x_4625_ == 0 {
                            leanh::lean_dec(v___x_4621_);
                            leanh::lean_dec(v_k_4606_);
                            leanh::lean_dec_ref(v_v_4605_);
                            return v_as_4607_;
                        } else {
                            let mut v___x_4626_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_x27_4627_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4628_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4629_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_inc(v___x_4622_);
                            v___x_4626_ = leanh::lean_box(0);
                            v_xs_x27_4627_ = lean_array_fset(v_as_4607_, v___x_4621_, v___x_4626_);
                            v___x_4628_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(v_x_4603_, v_keys_4604_, v_v_4605_, v_k_4606_, v___x_4622_);
                            v___x_4629_ = lean_array_fset(v_xs_x27_4627_, v___x_4621_, v___x_4628_);
                            leanh::lean_dec(v___x_4621_);
                            return v___x_4629_;
                        }
                    } else {
                        let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_4630_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(v_x_4603_, v_keys_4604_, v_v_4605_, v_k_4606_, v_as_4607_, v_k_4608_, v___x_4610_, v___x_4621_);
                        return v___x_4630_;
                    }
                } else {
                    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_4621_);
                    v___x_4631_ = leanh::lean_box(0);
                    v___x_4632_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_4603_, v_keys_4604_, v_v_4605_, v_k_4606_, v___x_4631_);
                    v___x_4633_ = lean_array_push(v_as_4607_, v___x_4632_);
                    return v___x_4633_;
                }
            }
        } else {
            let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_as_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4634_ = leanh::lean_box(0);
            v___x_4635_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_4603_, v_keys_4604_, v_v_4605_, v_k_4606_, v___x_4634_);
            v_as_4636_ = lean_array_push(v_as_4607_, v___x_4635_);
            v___x_4637_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                leanh::lean_box(0),
                v___x_4610_,
                v_as_4636_,
                v___x_4609_,
            );
            return v___x_4637_;
        }
    } else {
        let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4638_ = leanh::lean_box(0);
        v___x_4639_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__0(v_x_4603_, v_keys_4604_, v_v_4605_, v_k_4606_, v___x_4638_);
        v___x_4640_ = lean_array_push(v_as_4607_, v___x_4639_);
        return v___x_4640_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(
    mut v_keys_4641_: *mut leanh::LeanObject,
    mut v_v_4642_: *mut leanh::LeanObject,
    mut v_x_4643_: *mut leanh::LeanObject,
    mut v_x_4644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: u8 = 0;
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_4645_ = leanh::lean_ctor_get(v_x_4644_, 0);
                v_children_4646_ = leanh::lean_ctor_get(v_x_4644_, 1);
                v_isSharedCheck_4663_ = (!leanh::lean_is_exclusive(v_x_4644_)) as u8;
                if v_isSharedCheck_4663_ == 0 {
                    v___x_4648_ = v_x_4644_;
                    v_isShared_4649_ = v_isSharedCheck_4663_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_children_4646_);
                    leanh::lean_inc(v_vs_4645_);
                    leanh::lean_dec(v_x_4644_);
                    v___x_4648_ = leanh::lean_box(0);
                    v_isShared_4649_ = v_isSharedCheck_4663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4650_ = lean_array_get_size(v_keys_4641_);
                v___x_4651_ = lean_nat_dec_lt(v_x_4643_, v___x_4650_);
                if v___x_4651_ == 0 {
                    v___x_4652_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__21(v_vs_4645_, v_v_4642_);
                    if v_isShared_4649_ == 0 {
                        leanh::lean_ctor_set(v___x_4648_, 0, v___x_4652_);
                        v___x_4654_ = v___x_4648_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4655_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 1, v_children_4646_);
                        v___x_4654_ = v_reuseFailAlloc_4655_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_4656_ = lean_array_fget_borrowed(v_keys_4641_, v_x_4643_);
                    v___x_4657_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__1;
                    leanh::lean_inc_n(v_k_4656_, 2);
                    v___x_4658_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4658_, 0, v_k_4656_);
                    leanh::lean_ctor_set(v___x_4658_, 1, v___x_4657_);
                    v_c_4659_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22(v_x_4643_, v_keys_4641_, v_v_4642_, v_k_4656_, v_children_4646_, v___x_4658_);
                    leanh::lean_dec_ref_known(v___x_4658_, 2);
                    if v_isShared_4649_ == 0 {
                        leanh::lean_ctor_set(v___x_4648_, 1, v_c_4659_);
                        v___x_4661_ = v___x_4648_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4662_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4662_, 0, v_vs_4645_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4662_, 1, v_c_4659_);
                        v___x_4661_ = v_reuseFailAlloc_4662_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4654_;
            }
            3 => {
                return v___x_4661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(
    mut v_x_4664_: *mut leanh::LeanObject,
    mut v_keys_4665_: *mut leanh::LeanObject,
    mut v_v_4666_: *mut leanh::LeanObject,
    mut v_k_4667_: *mut leanh::LeanObject,
    mut v_x_4668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4672_: u8 = 0;
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut v_unused_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4669_ = leanh::lean_ctor_get(v_x_4668_, 1);
                v_isSharedCheck_4679_ = (!leanh::lean_is_exclusive(v_x_4668_)) as u8;
                if v_isSharedCheck_4679_ == 0 {
                    v_unused_4680_ = leanh::lean_ctor_get(v_x_4668_, 0);
                    leanh::lean_dec(v_unused_4680_);
                    v___x_4671_ = v_x_4668_;
                    v_isShared_4672_ = v_isSharedCheck_4679_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4669_);
                    leanh::lean_dec(v_x_4668_);
                    v___x_4671_ = leanh::lean_box(0);
                    v_isShared_4672_ = v_isSharedCheck_4679_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4673_ = leanh::lean_unsigned_to_nat(1);
                v___x_4674_ = lean_nat_add(v_x_4664_, v___x_4673_);
                v_c_4675_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_4665_, v_v_4666_, v___x_4674_, v_snd_4669_);
                leanh::lean_dec(v___x_4674_);
                if v_isShared_4672_ == 0 {
                    leanh::lean_ctor_set(v___x_4671_, 1, v_c_4675_);
                    leanh::lean_ctor_set(v___x_4671_, 0, v_k_4667_);
                    v___x_4677_ = v___x_4671_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4678_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_k_4667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 1, v_c_4675_);
                    v___x_4677_ = v_reuseFailAlloc_4678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2___boxed(
    mut v_x_4681_: *mut leanh::LeanObject,
    mut v_keys_4682_: *mut leanh::LeanObject,
    mut v_v_4683_: *mut leanh::LeanObject,
    mut v_k_4684_: *mut leanh::LeanObject,
    mut v_x_4685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4686_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___lam__2(v_x_4681_, v_keys_4682_, v_v_4683_, v_k_4684_, v_x_4685_);
    leanh::lean_dec_ref(v_keys_4682_);
    leanh::lean_dec(v_x_4681_);
    return v_res_4686_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___boxed(
    mut v_keys_4687_: *mut leanh::LeanObject,
    mut v_v_4688_: *mut leanh::LeanObject,
    mut v_x_4689_: *mut leanh::LeanObject,
    mut v_x_4690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4691_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_4687_, v_v_4688_, v_x_4689_, v_x_4690_);
    leanh::lean_dec(v_x_4689_);
    leanh::lean_dec_ref(v_keys_4687_);
    return v_res_4691_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg___boxed(
    mut v_x_4692_: *mut leanh::LeanObject,
    mut v_keys_4693_: *mut leanh::LeanObject,
    mut v_v_4694_: *mut leanh::LeanObject,
    mut v_k_4695_: *mut leanh::LeanObject,
    mut v_as_4696_: *mut leanh::LeanObject,
    mut v_k_4697_: *mut leanh::LeanObject,
    mut v_x_4698_: *mut leanh::LeanObject,
    mut v_x_4699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4700_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(v_x_4692_, v_keys_4693_, v_v_4694_, v_k_4695_, v_as_4696_, v_k_4697_, v_x_4698_, v_x_4699_);
    leanh::lean_dec_ref(v_k_4697_);
    leanh::lean_dec_ref(v_keys_4693_);
    leanh::lean_dec(v_x_4692_);
    return v_res_4700_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22___boxed(
    mut v_x_4701_: *mut leanh::LeanObject,
    mut v_keys_4702_: *mut leanh::LeanObject,
    mut v_v_4703_: *mut leanh::LeanObject,
    mut v_k_4704_: *mut leanh::LeanObject,
    mut v_as_4705_: *mut leanh::LeanObject,
    mut v_k_4706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4707_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22(v_x_4701_, v_keys_4702_, v_v_4703_, v_k_4704_, v_as_4705_, v_k_4706_);
    leanh::lean_dec_ref(v_k_4706_);
    leanh::lean_dec_ref(v_keys_4702_);
    leanh::lean_dec(v_x_4701_);
    return v_res_4707_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4711_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__2;
    v___x_4712_ = leanh::lean_unsigned_to_nat(23);
    v___x_4713_ = leanh::lean_unsigned_to_nat(166);
    v___x_4714_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__1;
    v___x_4715_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__0;
    v___x_4716_ = l_mkPanicMessageWithDecl(
        v___x_4715_,
        v___x_4714_,
        v___x_4713_,
        v___x_4712_,
        v___x_4711_,
    );
    return v___x_4716_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(
    mut v_d_4717_: *mut leanh::LeanObject,
    mut v_keys_4718_: *mut leanh::LeanObject,
    mut v_v_4719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: u8 = 0;
    v___x_4720_ = lean_array_get_size(v_keys_4718_);
    v___x_4721_ = leanh::lean_unsigned_to_nat(0);
    v___x_4722_ = lean_nat_dec_eq(v___x_4720_, v___x_4721_);
    if v___x_4722_ == 0 {
        let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4723_ = leanh::lean_box(0);
        v_k_4724_ = lean_array_get_borrowed(v___x_4723_, v_keys_4718_, v___x_4721_);
        v___x_4725_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(v_d_4717_, v_k_4724_);
        if leanh::lean_obj_tag(v___x_4725_) == 0 {
            let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4726_ = leanh::lean_unsigned_to_nat(1);
            v_c_4727_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                leanh::lean_box(0),
                v_keys_4718_,
                v_v_4719_,
                v___x_4726_,
            );
            leanh::lean_inc(v_k_4724_);
            v___x_4728_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(v_d_4717_, v_k_4724_, v_c_4727_);
            return v___x_4728_;
        } else {
            let mut v_val_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_4729_ = leanh::lean_ctor_get(v___x_4725_, 0);
            leanh::lean_inc(v_val_4729_);
            leanh::lean_dec_ref_known(v___x_4725_, 1);
            v___x_4730_ = leanh::lean_unsigned_to_nat(1);
            v_c_4731_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7(v_keys_4718_, v_v_4719_, v___x_4730_, v_val_4729_);
            leanh::lean_inc(v_k_4724_);
            v___x_4732_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(v_d_4717_, v_k_4724_, v_c_4731_);
            return v___x_4732_;
        }
    } else {
        let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_v_4719_);
        leanh::lean_dec_ref(v_d_4717_);
        v___x_4733_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___closed__3);
        v___x_4734_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__8(v___x_4733_);
        return v___x_4734_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2___boxed(
    mut v_d_4735_: *mut leanh::LeanObject,
    mut v_keys_4736_: *mut leanh::LeanObject,
    mut v_v_4737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_d_4735_, v_keys_4736_, v_v_4737_);
    leanh::lean_dec_ref(v_keys_4736_);
    return v_res_4738_;
}
pub unsafe fn l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(
    mut v_d_4739_: *mut leanh::LeanObject,
    mut v_p_4740_: *mut leanh::LeanObject,
    mut v_v_4741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keys_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keys_4742_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_p_4740_);
    v___x_4743_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2(v_d_4739_, v_keys_4742_, v_v_4741_);
    leanh::lean_dec_ref(v_keys_4742_);
    return v___x_4743_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: f64 = 0.0;
    v___x_4744_ = leanh::lean_unsigned_to_nat(0);
    v___x_4745_ = lean_float_of_nat(v___x_4744_);
    return v___x_4745_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(
    mut v_cls_4749_: *mut leanh::LeanObject,
    mut v_msg_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
    mut v___y_4752_: *mut leanh::LeanObject,
    mut v___y_4753_: *mut leanh::LeanObject,
    mut v___y_4754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4774_: u8 = 0;
    let mut v_tid_4775_: u64 = 0;
    let mut v_traces_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4779_: u8 = 0;
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: f64 = 0.0;
    let mut v___x_4782_: u8 = 0;
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4800_: u8 = 0;
    let mut v_isSharedCheck_4801_: u8 = 0;
    let mut v_isSharedCheck_4802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4756_ = leanh::lean_ctor_get(v___y_4753_, 5);
                v___x_4757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkTriplePatternFromExpr_spec__0_spec__0(v_msg_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
                v_a_4758_ = leanh::lean_ctor_get(v___x_4757_, 0);
                v_isSharedCheck_4802_ = (!leanh::lean_is_exclusive(v___x_4757_)) as u8;
                if v_isSharedCheck_4802_ == 0 {
                    v___x_4760_ = v___x_4757_;
                    v_isShared_4761_ = v_isSharedCheck_4802_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4758_);
                    leanh::lean_dec(v___x_4757_);
                    v___x_4760_ = leanh::lean_box(0);
                    v_isShared_4761_ = v_isSharedCheck_4802_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4762_ = lean_st_ref_take(v___y_4754_);
                v_traceState_4763_ = leanh::lean_ctor_get(v___x_4762_, 4);
                v_env_4764_ = leanh::lean_ctor_get(v___x_4762_, 0);
                v_nextMacroScope_4765_ = leanh::lean_ctor_get(v___x_4762_, 1);
                v_ngen_4766_ = leanh::lean_ctor_get(v___x_4762_, 2);
                v_auxDeclNGen_4767_ = leanh::lean_ctor_get(v___x_4762_, 3);
                v_cache_4768_ = leanh::lean_ctor_get(v___x_4762_, 5);
                v_messages_4769_ = leanh::lean_ctor_get(v___x_4762_, 6);
                v_infoState_4770_ = leanh::lean_ctor_get(v___x_4762_, 7);
                v_snapshotTasks_4771_ = leanh::lean_ctor_get(v___x_4762_, 8);
                v_isSharedCheck_4801_ = (!leanh::lean_is_exclusive(v___x_4762_)) as u8;
                if v_isSharedCheck_4801_ == 0 {
                    v___x_4773_ = v___x_4762_;
                    v_isShared_4774_ = v_isSharedCheck_4801_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4771_);
                    leanh::lean_inc(v_infoState_4770_);
                    leanh::lean_inc(v_messages_4769_);
                    leanh::lean_inc(v_cache_4768_);
                    leanh::lean_inc(v_traceState_4763_);
                    leanh::lean_inc(v_auxDeclNGen_4767_);
                    leanh::lean_inc(v_ngen_4766_);
                    leanh::lean_inc(v_nextMacroScope_4765_);
                    leanh::lean_inc(v_env_4764_);
                    leanh::lean_dec(v___x_4762_);
                    v___x_4773_ = leanh::lean_box(0);
                    v_isShared_4774_ = v_isSharedCheck_4801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4775_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4763_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4776_ = leanh::lean_ctor_get(v_traceState_4763_, 0);
                v_isSharedCheck_4800_ =
                    (!leanh::lean_is_exclusive(v_traceState_4763_)) as u8;
                if v_isSharedCheck_4800_ == 0 {
                    v___x_4778_ = v_traceState_4763_;
                    v_isShared_4779_ = v_isSharedCheck_4800_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4776_);
                    leanh::lean_dec(v_traceState_4763_);
                    v___x_4778_ = leanh::lean_box(0);
                    v_isShared_4779_ = v_isSharedCheck_4800_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4780_ = leanh::lean_box(0);
                v___x_4781_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__0);
                v___x_4782_ = 0;
                v___x_4783_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__1;
                v___x_4784_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4784_, 0, v_cls_4749_);
                leanh::lean_ctor_set(v___x_4784_, 1, v___x_4780_);
                leanh::lean_ctor_set(v___x_4784_, 2, v___x_4783_);
                leanh::lean_ctor_set_float(
                    v___x_4784_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4781_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4784_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4781_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4784_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4782_,
                );
                v___x_4785_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___closed__2;
                v___x_4786_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4786_, 0, v___x_4784_);
                leanh::lean_ctor_set(v___x_4786_, 1, v_a_4758_);
                leanh::lean_ctor_set(v___x_4786_, 2, v___x_4785_);
                leanh::lean_inc(v_ref_4756_);
                v___x_4787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4787_, 0, v_ref_4756_);
                leanh::lean_ctor_set(v___x_4787_, 1, v___x_4786_);
                v___x_4788_ = l_Lean_PersistentArray_push___redArg(v_traces_4776_, v___x_4787_);
                if v_isShared_4779_ == 0 {
                    leanh::lean_ctor_set(v___x_4778_, 0, v___x_4788_);
                    v___x_4790_ = v___x_4778_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4799_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4799_, 0, v___x_4788_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4799_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4775_,
                    );
                    v___x_4790_ = v_reuseFailAlloc_4799_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4774_ == 0 {
                    leanh::lean_ctor_set(v___x_4773_, 4, v___x_4790_);
                    v___x_4792_ = v___x_4773_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4798_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_env_4764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 1, v_nextMacroScope_4765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 2, v_ngen_4766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 3, v_auxDeclNGen_4767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 4, v___x_4790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 5, v_cache_4768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 6, v_messages_4769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 7, v_infoState_4770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 8, v_snapshotTasks_4771_);
                    v___x_4792_ = v_reuseFailAlloc_4798_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4793_ = lean_st_ref_set(v___y_4754_, v___x_4792_);
                v___x_4794_ = leanh::lean_box(0);
                if v_isShared_4761_ == 0 {
                    leanh::lean_ctor_set(v___x_4760_, 0, v___x_4794_);
                    v___x_4796_ = v___x_4760_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 0, v___x_4794_);
                    v___x_4796_ = v_reuseFailAlloc_4797_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg___boxed(
    mut v_cls_4803_: *mut leanh::LeanObject,
    mut v_msg_4804_: *mut leanh::LeanObject,
    mut v___y_4805_: *mut leanh::LeanObject,
    mut v___y_4806_: *mut leanh::LeanObject,
    mut v___y_4807_: *mut leanh::LeanObject,
    mut v___y_4808_: *mut leanh::LeanObject,
    mut v___y_4809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4810_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_4803_, v_msg_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
    leanh::lean_dec(v___y_4808_);
    leanh::lean_dec_ref(v___y_4807_);
    leanh::lean_dec(v___y_4806_);
    leanh::lean_dec_ref(v___y_4805_);
    return v_res_4810_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3;
    v___x_4823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__5;
    v___x_4824_ = l_Lean_Name_append(v___x_4823_, v___x_4822_);
    return v___x_4824_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4826_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__7;
    v___x_4827_ = l_Lean_stringToMessageData(v___x_4826_);
    return v___x_4827_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__9;
    v___x_4830_ = l_Lean_stringToMessageData(v___x_4829_);
    return v___x_4830_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(
    mut v_as_4831_: *mut leanh::LeanObject,
    mut v_sz_4832_: usize,
    mut v_i_4833_: usize,
    mut v_b_4834_: *mut leanh::LeanObject,
    mut v___y_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
    mut v___y_4837_: *mut leanh::LeanObject,
    mut v___y_4838_: *mut leanh::LeanObject,
    mut v___y_4839_: *mut leanh::LeanObject,
    mut v___y_4840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: usize = 0;
    let mut v___x_4845_: usize = 0;
    let mut v___x_4847_: u8 = 0;
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4861_: u8 = 0;
    let mut v___y_4863_: u8 = 0;
    let mut v_options_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4865_: u8 = 0;
    let mut v_inheritedTraceOptions_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: u8 = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4885_: u8 = 0;
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: u8 = 0;
    let mut v___x_4890_: u8 = 0;
    let mut v_isSharedCheck_4891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4847_ = lean_usize_dec_lt(v_i_4833_, v_sz_4832_);
                if v___x_4847_ == 0 {
                    v___x_4848_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4848_, 0, v_b_4834_);
                    return v___x_4848_;
                } else {
                    v_a_4849_ = lean_array_uget_borrowed(v_as_4831_, v_i_4833_);
                    v_origin_4850_ = leanh::lean_ctor_get(v_a_4849_, 4);
                    if leanh::lean_obj_tag(v_origin_4850_) == 0 {
                        v_priority_4851_ = leanh::lean_ctor_get(v_a_4849_, 3);
                        v_declName_4852_ = leanh::lean_ctor_get(v_origin_4850_, 0);
                        leanh::lean_inc(v_priority_4851_);
                        leanh::lean_inc(v_declName_4852_);
                        v___x_4853_ =
                            l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(
                                v_declName_4852_,
                                v_priority_4851_,
                                v___y_4837_,
                                v___y_4838_,
                                v___y_4839_,
                                v___y_4840_,
                            );
                        if leanh::lean_obj_tag(v___x_4853_) == 0 {
                            v_a_4854_ = leanh::lean_ctor_get(v___x_4853_, 0);
                            leanh::lean_inc(v_a_4854_);
                            leanh::lean_dec_ref_known(v___x_4853_, 1);
                            if leanh::lean_obj_tag(v_a_4854_) == 1 {
                                v_val_4855_ = leanh::lean_ctor_get(v_a_4854_, 0);
                                leanh::lean_inc(v_val_4855_);
                                leanh::lean_dec_ref_known(v_a_4854_, 1);
                                v_pattern_4856_ = leanh::lean_ctor_get(v_val_4855_, 0);
                                leanh::lean_inc_ref(v_pattern_4856_);
                                v___x_4857_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_4834_, v_pattern_4856_, v_val_4855_);
                                v_a_4843_ = v___x_4857_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_4854_);
                                v_a_4843_ = v_b_4834_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4858_ = leanh::lean_ctor_get(v___x_4853_, 0);
                            v_isSharedCheck_4891_ =
                                (!leanh::lean_is_exclusive(v___x_4853_)) as u8;
                            if v_isSharedCheck_4891_ == 0 {
                                v___x_4860_ = v___x_4853_;
                                v_isShared_4861_ = v_isSharedCheck_4891_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4858_);
                                leanh::lean_dec(v___x_4853_);
                                v___x_4860_ = leanh::lean_box(0);
                                v_isShared_4861_ = v_isSharedCheck_4891_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v_a_4843_ = v_b_4834_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4844_ = 1usize;
                v___x_4845_ = lean_usize_add(v_i_4833_, v___x_4844_);
                v_i_4833_ = v___x_4845_;
                v_b_4834_ = v_a_4843_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4889_ = l_Lean_Exception_isInterrupt(v_a_4858_);
                if v___x_4889_ == 0 {
                    leanh::lean_inc(v_a_4858_);
                    v___x_4890_ = l_Lean_Exception_isRuntime(v_a_4858_);
                    v___y_4863_ = v___x_4890_;
                    state = 3;
                    continue;
                } else {
                    v___y_4863_ = v___x_4889_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_4863_ == 0 {
                    leanh::lean_del_object(v___x_4860_);
                    v_options_4864_ = leanh::lean_ctor_get(v___y_4839_, 2);
                    v_hasTrace_4865_ = leanh::lean_ctor_get_uint8(
                        v_options_4864_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4865_ == 0 {
                        leanh::lean_dec(v_a_4858_);
                        v_a_4843_ = v_b_4834_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4866_ =
                            leanh::lean_ctor_get(v___y_4839_, 13);
                        v___x_4867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3;
                        v___x_4868_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
                        v___x_4869_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4866_,
                            v_options_4864_,
                            v___x_4868_,
                        );
                        if v___x_4869_ == 0 {
                            leanh::lean_dec(v_a_4858_);
                            v_a_4843_ = v_b_4834_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4870_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__8);
                            leanh::lean_inc(v_declName_4852_);
                            v___x_4871_ = l_Lean_MessageData_ofName(v_declName_4852_);
                            v___x_4872_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4872_, 0, v___x_4870_);
                            leanh::lean_ctor_set(v___x_4872_, 1, v___x_4871_);
                            v___x_4873_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
                            v___x_4874_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4874_, 0, v___x_4872_);
                            leanh::lean_ctor_set(v___x_4874_, 1, v___x_4873_);
                            v___x_4875_ = l_Lean_Exception_toMessageData(v_a_4858_);
                            v___x_4876_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4876_, 0, v___x_4874_);
                            leanh::lean_ctor_set(v___x_4876_, 1, v___x_4875_);
                            v___x_4877_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_4867_, v___x_4876_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
                            if leanh::lean_obj_tag(v___x_4877_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4877_, 1);
                                v_a_4843_ = v_b_4834_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_4834_);
                                v_a_4878_ = leanh::lean_ctor_get(v___x_4877_, 0);
                                v_isSharedCheck_4885_ =
                                    (!leanh::lean_is_exclusive(v___x_4877_)) as u8;
                                if v_isSharedCheck_4885_ == 0 {
                                    v___x_4880_ = v___x_4877_;
                                    v_isShared_4881_ = v_isSharedCheck_4885_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4878_);
                                    leanh::lean_dec(v___x_4877_);
                                    v___x_4880_ = leanh::lean_box(0);
                                    v_isShared_4881_ = v_isSharedCheck_4885_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_4834_);
                    if v_isShared_4861_ == 0 {
                        v___x_4887_ = v___x_4860_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4888_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4858_);
                        v___x_4887_ = v_reuseFailAlloc_4888_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4881_ == 0 {
                    v___x_4883_ = v___x_4880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4884_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4878_);
                    v___x_4883_ = v_reuseFailAlloc_4884_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4883_;
            }
            6 => {
                return v___x_4887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___boxed(
    mut v_as_4892_: *mut leanh::LeanObject,
    mut v_sz_4893_: *mut leanh::LeanObject,
    mut v_i_4894_: *mut leanh::LeanObject,
    mut v_b_4895_: *mut leanh::LeanObject,
    mut v___y_4896_: *mut leanh::LeanObject,
    mut v___y_4897_: *mut leanh::LeanObject,
    mut v___y_4898_: *mut leanh::LeanObject,
    mut v___y_4899_: *mut leanh::LeanObject,
    mut v___y_4900_: *mut leanh::LeanObject,
    mut v___y_4901_: *mut leanh::LeanObject,
    mut v___y_4902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4903_: usize = 0;
    let mut v_i_boxed_4904_: usize = 0;
    let mut v_res_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4903_ = leanh::lean_unbox_usize(v_sz_4893_);
    leanh::lean_dec(v_sz_4893_);
    v_i_boxed_4904_ = leanh::lean_unbox_usize(v_i_4894_);
    leanh::lean_dec(v_i_4894_);
    v_res_4905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v_as_4892_, v_sz_boxed_4903_, v_i_boxed_4904_, v_b_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_);
    leanh::lean_dec(v___y_4901_);
    leanh::lean_dec_ref(v___y_4900_);
    leanh::lean_dec(v___y_4899_);
    leanh::lean_dec_ref(v___y_4898_);
    leanh::lean_dec(v___y_4897_);
    leanh::lean_dec_ref(v___y_4896_);
    leanh::lean_dec_ref(v_as_4892_);
    return v_res_4905_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(
    mut v_a_4906_: *mut leanh::LeanObject,
    mut v_a_4907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4913_: u8 = 0;
    let mut v_fst_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4906_) == 0 {
                    v___x_4908_ = l_List_reverse___redArg(v_a_4907_);
                    return v___x_4908_;
                } else {
                    v_head_4909_ = leanh::lean_ctor_get(v_a_4906_, 0);
                    v_tail_4910_ = leanh::lean_ctor_get(v_a_4906_, 1);
                    v_isSharedCheck_4919_ = (!leanh::lean_is_exclusive(v_a_4906_)) as u8;
                    if v_isSharedCheck_4919_ == 0 {
                        v___x_4912_ = v_a_4906_;
                        v_isShared_4913_ = v_isSharedCheck_4919_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4910_);
                        leanh::lean_inc(v_head_4909_);
                        leanh::lean_dec(v_a_4906_);
                        v___x_4912_ = leanh::lean_box(0);
                        v_isShared_4913_ = v_isSharedCheck_4919_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4914_ = leanh::lean_ctor_get(v_head_4909_, 0);
                leanh::lean_inc(v_fst_4914_);
                leanh::lean_dec(v_head_4909_);
                if v_isShared_4913_ == 0 {
                    leanh::lean_ctor_set(v___x_4912_, 1, v_a_4907_);
                    leanh::lean_ctor_set(v___x_4912_, 0, v_fst_4914_);
                    v___x_4916_ = v___x_4912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4918_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_fst_4914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 1, v_a_4907_);
                    v___x_4916_ = v_reuseFailAlloc_4918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4906_ = v_tail_4910_;
                v_a_4907_ = v___x_4916_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(
    mut v_f_4920_: *mut leanh::LeanObject,
    mut v_keys_4921_: *mut leanh::LeanObject,
    mut v_vals_4922_: *mut leanh::LeanObject,
    mut v_i_4923_: *mut leanh::LeanObject,
    mut v_acc_4924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    let mut v_k_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4925_ = lean_array_get_size(v_keys_4921_);
                v___x_4926_ = lean_nat_dec_lt(v_i_4923_, v___x_4925_);
                if v___x_4926_ == 0 {
                    leanh::lean_dec(v_i_4923_);
                    leanh::lean_dec(v_f_4920_);
                    return v_acc_4924_;
                } else {
                    v_k_4927_ = lean_array_fget_borrowed(v_keys_4921_, v_i_4923_);
                    v_v_4928_ = lean_array_fget_borrowed(v_vals_4922_, v_i_4923_);
                    leanh::lean_inc(v_f_4920_);
                    leanh::lean_inc(v_v_4928_);
                    leanh::lean_inc(v_k_4927_);
                    v___x_4929_ =
                        leanh::lean_apply_3(v_f_4920_, v_acc_4924_, v_k_4927_, v_v_4928_);
                    v___x_4930_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4931_ = lean_nat_add(v_i_4923_, v___x_4930_);
                    leanh::lean_dec(v_i_4923_);
                    v_i_4923_ = v___x_4931_;
                    v_acc_4924_ = v___x_4929_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg___boxed(
    mut v_f_4933_: *mut leanh::LeanObject,
    mut v_keys_4934_: *mut leanh::LeanObject,
    mut v_vals_4935_: *mut leanh::LeanObject,
    mut v_i_4936_: *mut leanh::LeanObject,
    mut v_acc_4937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4938_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(v_f_4933_, v_keys_4934_, v_vals_4935_, v_i_4936_, v_acc_4937_);
    leanh::lean_dec_ref(v_vals_4935_);
    leanh::lean_dec_ref(v_keys_4934_);
    return v_res_4938_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(
    mut v_f_4939_: *mut leanh::LeanObject,
    mut v_x_4940_: *mut leanh::LeanObject,
    mut v_x_4941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4940_) == 0 {
        let mut v_es_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4945_: u8 = 0;
        v_es_4942_ = leanh::lean_ctor_get(v_x_4940_, 0);
        v___x_4943_ = leanh::lean_unsigned_to_nat(0);
        v___x_4944_ = lean_array_get_size(v_es_4942_);
        v___x_4945_ = lean_nat_dec_lt(v___x_4943_, v___x_4944_);
        if v___x_4945_ == 0 {
            leanh::lean_dec(v_f_4939_);
            return v_x_4941_;
        } else {
            let mut v___x_4946_: u8 = 0;
            v___x_4946_ = lean_nat_dec_le(v___x_4944_, v___x_4944_);
            if v___x_4946_ == 0 {
                if v___x_4945_ == 0 {
                    leanh::lean_dec(v_f_4939_);
                    return v_x_4941_;
                } else {
                    let mut v___x_4947_: usize = 0;
                    let mut v___x_4948_: usize = 0;
                    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4947_ = 0usize;
                    v___x_4948_ = lean_usize_of_nat(v___x_4944_);
                    v___x_4949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_4939_, v_es_4942_, v___x_4947_, v___x_4948_, v_x_4941_);
                    return v___x_4949_;
                }
            } else {
                let mut v___x_4950_: usize = 0;
                let mut v___x_4951_: usize = 0;
                let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_4950_ = 0usize;
                v___x_4951_ = lean_usize_of_nat(v___x_4944_);
                v___x_4952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_4939_, v_es_4942_, v___x_4950_, v___x_4951_, v_x_4941_);
                return v___x_4952_;
            }
        }
    } else {
        let mut v_ks_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ks_4953_ = leanh::lean_ctor_get(v_x_4940_, 0);
        v_vs_4954_ = leanh::lean_ctor_get(v_x_4940_, 1);
        v___x_4955_ = leanh::lean_unsigned_to_nat(0);
        v___x_4956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(v_f_4939_, v_ks_4953_, v_vs_4954_, v___x_4955_, v_x_4941_);
        return v___x_4956_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(
    mut v_f_4957_: *mut leanh::LeanObject,
    mut v_as_4958_: *mut leanh::LeanObject,
    mut v_i_4959_: usize,
    mut v_stop_4960_: usize,
    mut v_b_4961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: usize = 0;
    let mut v___x_4965_: usize = 0;
    let mut v___x_4967_: u8 = 0;
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4967_ = lean_usize_dec_eq(v_i_4959_, v_stop_4960_);
                if v___x_4967_ == 0 {
                    v___x_4968_ = lean_array_uget_borrowed(v_as_4958_, v_i_4959_);
                    match leanh::lean_obj_tag(v___x_4968_) {
                        0 => {
                            v_key_4969_ = leanh::lean_ctor_get(v___x_4968_, 0);
                            v_val_4970_ = leanh::lean_ctor_get(v___x_4968_, 1);
                            leanh::lean_inc(v_f_4957_);
                            leanh::lean_inc(v_val_4970_);
                            leanh::lean_inc(v_key_4969_);
                            v___x_4971_ = leanh::lean_apply_3(
                                v_f_4957_,
                                v_b_4961_,
                                v_key_4969_,
                                v_val_4970_,
                            );
                            v___y_4963_ = v___x_4971_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_4972_ = leanh::lean_ctor_get(v___x_4968_, 0);
                            leanh::lean_inc(v_f_4957_);
                            v___x_4973_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_4957_, v_node_4972_, v_b_4961_);
                            v___y_4963_ = v___x_4973_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_4963_ = v_b_4961_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_f_4957_);
                    return v_b_4961_;
                }
            }
            1 => {
                v___x_4964_ = 1usize;
                v___x_4965_ = lean_usize_add(v_i_4959_, v___x_4964_);
                v_i_4959_ = v___x_4965_;
                v_b_4961_ = v___y_4963_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg___boxed(
    mut v_f_4974_: *mut leanh::LeanObject,
    mut v_as_4975_: *mut leanh::LeanObject,
    mut v_i_4976_: *mut leanh::LeanObject,
    mut v_stop_4977_: *mut leanh::LeanObject,
    mut v_b_4978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4979_: usize = 0;
    let mut v_stop_boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4979_ = leanh::lean_unbox_usize(v_i_4976_);
    leanh::lean_dec(v_i_4976_);
    v_stop_boxed_4980_ = leanh::lean_unbox_usize(v_stop_4977_);
    leanh::lean_dec(v_stop_4977_);
    v_res_4981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_4974_, v_as_4975_, v_i_boxed_4979_, v_stop_boxed_4980_, v_b_4978_);
    leanh::lean_dec_ref(v_as_4975_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg___boxed(
    mut v_f_4982_: *mut leanh::LeanObject,
    mut v_x_4983_: *mut leanh::LeanObject,
    mut v_x_4984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4985_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_4982_, v_x_4983_, v_x_4984_);
    leanh::lean_dec_ref(v_x_4983_);
    return v_res_4985_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___lam__0(
    mut v_f_4986_: *mut leanh::LeanObject,
    mut v_x1_4987_: *mut leanh::LeanObject,
    mut v_x2_4988_: *mut leanh::LeanObject,
    mut v_x3_4989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4990_ = leanh::lean_apply_3(v_f_4986_, v_x1_4987_, v_x2_4988_, v_x3_4989_);
    return v___x_4990_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(
    mut v_map_4991_: *mut leanh::LeanObject,
    mut v_f_4992_: *mut leanh::LeanObject,
    mut v_init_4993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4994_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_4994_, 0, v_f_4992_);
    v___x_4995_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_4994_, v_map_4991_, v_init_4993_);
    return v___x_4995_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg___boxed(
    mut v_map_4996_: *mut leanh::LeanObject,
    mut v_f_4997_: *mut leanh::LeanObject,
    mut v_init_4998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4999_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(v_map_4996_, v_f_4997_, v_init_4998_);
    leanh::lean_dec_ref(v_map_4996_);
    return v_res_4999_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___lam__0(
    mut v_ps_5000_: *mut leanh::LeanObject,
    mut v_k_5001_: *mut leanh::LeanObject,
    mut v_v_5002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5003_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5003_, 0, v_k_5001_);
    leanh::lean_ctor_set(v___x_5003_, 1, v_v_5002_);
    v___x_5004_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5004_, 0, v___x_5003_);
    leanh::lean_ctor_set(v___x_5004_, 1, v_ps_5000_);
    return v___x_5004_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(
    mut v_m_5006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5007_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___closed__0;
    v___x_5008_ = leanh::lean_box(0);
    v___x_5009_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(v_m_5006_, v___f_5007_, v___x_5008_);
    return v___x_5009_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg___boxed(
    mut v_m_5010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5011_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_5010_);
    leanh::lean_dec_ref(v_m_5010_);
    return v_res_5011_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(
    mut v_s_5012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5013_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_s_5012_);
    v___x_5014_ = leanh::lean_box(0);
    v___x_5015_ = l_List_mapTR_loop___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__16(v___x_5013_, v___x_5014_);
    return v___x_5015_;
}
pub unsafe fn l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9___boxed(
    mut v_s_5016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5017_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_s_5016_);
    leanh::lean_dec_ref(v_s_5016_);
    return v_res_5017_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5019_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__0;
    v___x_5020_ = l_Lean_stringToMessageData(v___x_5019_);
    return v___x_5020_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__2;
    v___x_5023_ = l_Lean_stringToMessageData(v___x_5022_);
    return v___x_5023_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__4;
    v___x_5026_ = l_Lean_stringToMessageData(v___x_5025_);
    return v___x_5026_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__6;
    v___x_5029_ = l_Lean_stringToMessageData(v___x_5028_);
    return v___x_5029_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__8;
    v___x_5032_ = l_Lean_stringToMessageData(v___x_5031_);
    return v___x_5032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(
    mut v_as_5033_: *mut leanh::LeanObject,
    mut v_sz_5034_: usize,
    mut v_i_5035_: usize,
    mut v_b_5036_: *mut leanh::LeanObject,
    mut v___y_5037_: *mut leanh::LeanObject,
    mut v___y_5038_: *mut leanh::LeanObject,
    mut v___y_5039_: *mut leanh::LeanObject,
    mut v___y_5040_: *mut leanh::LeanObject,
    mut v___y_5041_: *mut leanh::LeanObject,
    mut v___y_5042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: usize = 0;
    let mut v___x_5047_: usize = 0;
    let mut v___x_5049_: u8 = 0;
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5067_: u8 = 0;
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut v_declName_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5049_ = lean_usize_dec_lt(v_i_5035_, v_sz_5034_);
                if v___x_5049_ == 0 {
                    v___x_5050_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5050_, 0, v_b_5036_);
                    return v___x_5050_;
                } else {
                    v_a_5051_ = lean_array_uget_borrowed(v_as_5033_, v_i_5035_);
                    v_proof_5052_ = leanh::lean_ctor_get(v_a_5051_, 2);
                    v_priority_5053_ = leanh::lean_ctor_get(v_a_5051_, 4);
                    leanh::lean_inc(v_priority_5053_);
                    leanh::lean_inc_ref(v_proof_5052_);
                    v___x_5054_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew(
                        v_proof_5052_,
                        v_priority_5053_,
                        v___y_5037_,
                        v___y_5038_,
                        v___y_5039_,
                        v___y_5040_,
                        v___y_5041_,
                        v___y_5042_,
                    );
                    if leanh::lean_obj_tag(v___x_5054_) == 0 {
                        v_a_5055_ = leanh::lean_ctor_get(v___x_5054_, 0);
                        leanh::lean_inc(v_a_5055_);
                        leanh::lean_dec_ref_known(v___x_5054_, 1);
                        if leanh::lean_obj_tag(v_a_5055_) == 1 {
                            v_val_5056_ = leanh::lean_ctor_get(v_a_5055_, 0);
                            leanh::lean_inc(v_val_5056_);
                            leanh::lean_dec_ref_known(v_a_5055_, 1);
                            v_pattern_5057_ = leanh::lean_ctor_get(v_val_5056_, 0);
                            leanh::lean_inc_ref(v_pattern_5057_);
                            v___x_5058_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_5036_, v_pattern_5057_, v_val_5056_);
                            v_a_5045_ = v___x_5058_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_5055_);
                            v___x_5059_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__1);
                            match leanh::lean_obj_tag(v_proof_5052_) {
                                0 => {
                                    v_declName_5072_ =
                                        leanh::lean_ctor_get(v_proof_5052_, 0);
                                    v___x_5073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__3);
                                    leanh::lean_inc(v_declName_5072_);
                                    v___x_5074_ = l_Lean_MessageData_ofName(v_declName_5072_);
                                    v___x_5075_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5075_, 0, v___x_5073_);
                                    leanh::lean_ctor_set(v___x_5075_, 1, v___x_5074_);
                                    v___y_5061_ = v___x_5075_;
                                    state = 2;
                                    continue;
                                }
                                1 => {
                                    v_fvarId_5076_ = leanh::lean_ctor_get(v_proof_5052_, 0);
                                    v___x_5077_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__5);
                                    leanh::lean_inc(v_fvarId_5076_);
                                    v___x_5078_ = l_Lean_mkFVar(v_fvarId_5076_);
                                    v___x_5079_ = l_Lean_MessageData_ofExpr(v___x_5078_);
                                    v___x_5080_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5080_, 0, v___x_5077_);
                                    leanh::lean_ctor_set(v___x_5080_, 1, v___x_5079_);
                                    v___y_5061_ = v___x_5080_;
                                    state = 2;
                                    continue;
                                }
                                _ => {
                                    v_ref_5081_ = leanh::lean_ctor_get(v_proof_5052_, 1);
                                    v_proof_5082_ = leanh::lean_ctor_get(v_proof_5052_, 2);
                                    v___x_5083_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__7);
                                    leanh::lean_inc(v_ref_5081_);
                                    v___x_5084_ = l_Lean_MessageData_ofSyntax(v_ref_5081_);
                                    v___x_5085_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5085_, 0, v___x_5083_);
                                    leanh::lean_ctor_set(v___x_5085_, 1, v___x_5084_);
                                    v___x_5086_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___closed__9);
                                    v___x_5087_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5087_, 0, v___x_5085_);
                                    leanh::lean_ctor_set(v___x_5087_, 1, v___x_5086_);
                                    leanh::lean_inc_ref(v_proof_5082_);
                                    v___x_5088_ = l_Lean_MessageData_ofExpr(v_proof_5082_);
                                    v___x_5089_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5089_, 0, v___x_5087_);
                                    leanh::lean_ctor_set(v___x_5089_, 1, v___x_5088_);
                                    v___y_5061_ = v___x_5089_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_5036_);
                        v_a_5090_ = leanh::lean_ctor_get(v___x_5054_, 0);
                        v_isSharedCheck_5097_ =
                            (!leanh::lean_is_exclusive(v___x_5054_)) as u8;
                        if v_isSharedCheck_5097_ == 0 {
                            v___x_5092_ = v___x_5054_;
                            v_isShared_5093_ = v_isSharedCheck_5097_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5090_);
                            leanh::lean_dec(v___x_5054_);
                            v___x_5092_ = leanh::lean_box(0);
                            v_isShared_5093_ = v_isSharedCheck_5097_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5046_ = 1usize;
                v___x_5047_ = lean_usize_add(v_i_5035_, v___x_5046_);
                v_i_5035_ = v___x_5047_;
                v_b_5036_ = v_a_5045_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5062_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5062_, 0, v___x_5059_);
                leanh::lean_ctor_set(v___x_5062_, 1, v___y_5061_);
                v___x_5063_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__1___redArg(v___x_5062_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
                if leanh::lean_obj_tag(v___x_5063_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5063_, 1);
                    v_a_5045_ = v_b_5036_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_5036_);
                    v_a_5064_ = leanh::lean_ctor_get(v___x_5063_, 0);
                    v_isSharedCheck_5071_ = (!leanh::lean_is_exclusive(v___x_5063_)) as u8;
                    if v_isSharedCheck_5071_ == 0 {
                        v___x_5066_ = v___x_5063_;
                        v_isShared_5067_ = v_isSharedCheck_5071_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5064_);
                        leanh::lean_dec(v___x_5063_);
                        v___x_5066_ = leanh::lean_box(0);
                        v_isShared_5067_ = v_isSharedCheck_5071_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5067_ == 0 {
                    v___x_5069_ = v___x_5066_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_a_5064_);
                    v___x_5069_ = v_reuseFailAlloc_5070_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5069_;
            }
            5 => {
                if v_isShared_5093_ == 0 {
                    v___x_5095_ = v___x_5092_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5096_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5096_, 0, v_a_5090_);
                    v___x_5095_ = v_reuseFailAlloc_5096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7___boxed(
    mut v_as_5098_: *mut leanh::LeanObject,
    mut v_sz_5099_: *mut leanh::LeanObject,
    mut v_i_5100_: *mut leanh::LeanObject,
    mut v_b_5101_: *mut leanh::LeanObject,
    mut v___y_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
    mut v___y_5105_: *mut leanh::LeanObject,
    mut v___y_5106_: *mut leanh::LeanObject,
    mut v___y_5107_: *mut leanh::LeanObject,
    mut v___y_5108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5109_: usize = 0;
    let mut v_i_boxed_5110_: usize = 0;
    let mut v_res_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5109_ = leanh::lean_unbox_usize(v_sz_5099_);
    leanh::lean_dec(v_sz_5099_);
    v_i_boxed_5110_ = leanh::lean_unbox_usize(v_i_5100_);
    leanh::lean_dec(v_i_5100_);
    v_res_5111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v_as_5098_, v_sz_boxed_5109_, v_i_boxed_5110_, v_b_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
    leanh::lean_dec(v___y_5107_);
    leanh::lean_dec_ref(v___y_5106_);
    leanh::lean_dec(v___y_5105_);
    leanh::lean_dec_ref(v___y_5104_);
    leanh::lean_dec(v___y_5103_);
    leanh::lean_dec_ref(v___y_5102_);
    leanh::lean_dec_ref(v_as_5098_);
    return v_res_5111_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(
    mut v_keys_5112_: *mut leanh::LeanObject,
    mut v_vals_5113_: *mut leanh::LeanObject,
    mut v_i_5114_: *mut leanh::LeanObject,
    mut v_k_5115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u8 = 0;
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: u8 = 0;
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5116_ = lean_array_get_size(v_keys_5112_);
                v___x_5117_ = lean_nat_dec_lt(v_i_5114_, v___x_5116_);
                if v___x_5117_ == 0 {
                    leanh::lean_dec(v_i_5114_);
                    v___x_5118_ = leanh::lean_box(0);
                    return v___x_5118_;
                } else {
                    v_k_x27_5119_ = lean_array_fget_borrowed(v_keys_5112_, v_i_5114_);
                    v___x_5120_ = lean_name_eq(v_k_5115_, v_k_x27_5119_);
                    if v___x_5120_ == 0 {
                        v___x_5121_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5122_ = lean_nat_add(v_i_5114_, v___x_5121_);
                        leanh::lean_dec(v_i_5114_);
                        v_i_5114_ = v___x_5122_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5124_ = lean_array_fget_borrowed(v_vals_5113_, v_i_5114_);
                        leanh::lean_dec(v_i_5114_);
                        leanh::lean_inc(v___x_5124_);
                        v___x_5125_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5125_, 0, v___x_5124_);
                        return v___x_5125_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg___boxed(
    mut v_keys_5126_: *mut leanh::LeanObject,
    mut v_vals_5127_: *mut leanh::LeanObject,
    mut v_i_5128_: *mut leanh::LeanObject,
    mut v_k_5129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(v_keys_5126_, v_vals_5127_, v_i_5128_, v_k_5129_);
    leanh::lean_dec(v_k_5129_);
    leanh::lean_dec_ref(v_vals_5127_);
    leanh::lean_dec_ref(v_keys_5126_);
    return v_res_5130_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(
    mut v_x_5131_: *mut leanh::LeanObject,
    mut v_x_5132_: usize,
    mut v_x_5133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: usize = 0;
    let mut v___x_5137_: usize = 0;
    let mut v___x_5138_: usize = 0;
    let mut v_j_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: usize = 0;
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5131_) == 0 {
                    v_es_5134_ = leanh::lean_ctor_get(v_x_5131_, 0);
                    v___x_5135_ = leanh::lean_box(2);
                    v___x_5136_ = 5usize;
                    v___x_5137_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
                    v___x_5138_ = lean_usize_land(v_x_5132_, v___x_5137_);
                    v_j_5139_ = lean_usize_to_nat(v___x_5138_);
                    v___x_5140_ = lean_array_get_borrowed(v___x_5135_, v_es_5134_, v_j_5139_);
                    leanh::lean_dec(v_j_5139_);
                    match leanh::lean_obj_tag(v___x_5140_) {
                        0 => {
                            v_key_5141_ = leanh::lean_ctor_get(v___x_5140_, 0);
                            v_val_5142_ = leanh::lean_ctor_get(v___x_5140_, 1);
                            v___x_5143_ = lean_name_eq(v_x_5133_, v_key_5141_);
                            if v___x_5143_ == 0 {
                                v___x_5144_ = leanh::lean_box(0);
                                return v___x_5144_;
                            } else {
                                leanh::lean_inc(v_val_5142_);
                                v___x_5145_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5145_, 0, v_val_5142_);
                                return v___x_5145_;
                            }
                        }
                        1 => {
                            v_node_5146_ = leanh::lean_ctor_get(v___x_5140_, 0);
                            v___x_5147_ = lean_usize_shift_right(v_x_5132_, v___x_5136_);
                            v_x_5131_ = v_node_5146_;
                            v_x_5132_ = v___x_5147_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5149_ = leanh::lean_box(0);
                            return v___x_5149_;
                        }
                    }
                } else {
                    v_ks_5150_ = leanh::lean_ctor_get(v_x_5131_, 0);
                    v_vs_5151_ = leanh::lean_ctor_get(v_x_5131_, 1);
                    v___x_5152_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(v_ks_5150_, v_vs_5151_, v___x_5152_, v_x_5133_);
                    return v___x_5153_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg___boxed(
    mut v_x_5154_: *mut leanh::LeanObject,
    mut v_x_5155_: *mut leanh::LeanObject,
    mut v_x_5156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_27997__boxed_5157_: usize = 0;
    let mut v_res_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_27997__boxed_5157_ = leanh::lean_unbox_usize(v_x_5155_);
    leanh::lean_dec(v_x_5155_);
    v_res_5158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_5154_, v_x_27997__boxed_5157_, v_x_5156_);
    leanh::lean_dec(v_x_5156_);
    leanh::lean_dec_ref(v_x_5154_);
    return v_res_5158_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(
    mut v_x_5159_: *mut leanh::LeanObject,
    mut v_x_5160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5162_: u64 = 0;
    let mut v___x_5163_: usize = 0;
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: u64 = 0;
    let mut v_hash_5166_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5160_) == 0 {
                    v___x_5165_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_5162_ = v___x_5165_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5166_ = leanh::lean_ctor_get_uint64(
                        v_x_5160_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5162_ = v_hash_5166_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5163_ = lean_uint64_to_usize(v___y_5162_);
                v___x_5164_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_5159_, v___x_5163_, v_x_5160_);
                return v___x_5164_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg___boxed(
    mut v_x_5167_: *mut leanh::LeanObject,
    mut v_x_5168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5169_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_5167_, v_x_5168_);
    leanh::lean_dec(v_x_5168_);
    leanh::lean_dec_ref(v_x_5167_);
    return v_res_5169_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__0;
    v___x_5172_ = l_Lean_stringToMessageData(v___x_5171_);
    return v___x_5172_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__2;
    v___x_5175_ = l_Lean_stringToMessageData(v___x_5174_);
    return v___x_5175_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(
    mut v_a_5176_: *mut leanh::LeanObject,
    mut v_as_5177_: *mut leanh::LeanObject,
    mut v_sz_5178_: usize,
    mut v_i_5179_: usize,
    mut v_b_5180_: *mut leanh::LeanObject,
    mut v___y_5181_: *mut leanh::LeanObject,
    mut v___y_5182_: *mut leanh::LeanObject,
    mut v___y_5183_: *mut leanh::LeanObject,
    mut v___y_5184_: *mut leanh::LeanObject,
    mut v___y_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: usize = 0;
    let mut v___x_5191_: usize = 0;
    let mut v___x_5193_: u8 = 0;
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5205_: u8 = 0;
    let mut v___y_5207_: u8 = 0;
    let mut v_options_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5209_: u8 = 0;
    let mut v_inheritedTraceOptions_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: u8 = 0;
    let mut v___x_5238_: u8 = 0;
    let mut v_isSharedCheck_5239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5193_ = lean_usize_dec_lt(v_i_5179_, v_sz_5178_);
                if v___x_5193_ == 0 {
                    leanh::lean_dec(v_a_5176_);
                    v___x_5194_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5194_, 0, v_b_5180_);
                    return v___x_5194_;
                } else {
                    v_a_5195_ = lean_array_uget_borrowed(v_as_5177_, v_i_5179_);
                    v___x_5196_ = leanh::lean_unsigned_to_nat(1000);
                    leanh::lean_inc(v_a_5195_);
                    v___x_5197_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNewFromSimpDecl_x3f(
                        v_a_5195_,
                        v___x_5196_,
                        v___y_5183_,
                        v___y_5184_,
                        v___y_5185_,
                        v___y_5186_,
                    );
                    if leanh::lean_obj_tag(v___x_5197_) == 0 {
                        v_a_5198_ = leanh::lean_ctor_get(v___x_5197_, 0);
                        leanh::lean_inc(v_a_5198_);
                        leanh::lean_dec_ref_known(v___x_5197_, 1);
                        if leanh::lean_obj_tag(v_a_5198_) == 1 {
                            v_val_5199_ = leanh::lean_ctor_get(v_a_5198_, 0);
                            leanh::lean_inc(v_val_5199_);
                            leanh::lean_dec_ref_known(v_a_5198_, 1);
                            v_pattern_5200_ = leanh::lean_ctor_get(v_val_5199_, 0);
                            leanh::lean_inc_ref(v_pattern_5200_);
                            v___x_5201_ = l_Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1(v_b_5180_, v_pattern_5200_, v_val_5199_);
                            v_snd_5189_ = v___x_5201_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_5198_);
                            v_snd_5189_ = v_b_5180_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5202_ = leanh::lean_ctor_get(v___x_5197_, 0);
                        v_isSharedCheck_5239_ =
                            (!leanh::lean_is_exclusive(v___x_5197_)) as u8;
                        if v_isSharedCheck_5239_ == 0 {
                            v___x_5204_ = v___x_5197_;
                            v_isShared_5205_ = v_isSharedCheck_5239_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5202_);
                            leanh::lean_dec(v___x_5197_);
                            v___x_5204_ = leanh::lean_box(0);
                            v_isShared_5205_ = v_isSharedCheck_5239_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5190_ = 1usize;
                v___x_5191_ = lean_usize_add(v_i_5179_, v___x_5190_);
                v_i_5179_ = v___x_5191_;
                v_b_5180_ = v_snd_5189_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5237_ = l_Lean_Exception_isInterrupt(v_a_5202_);
                if v___x_5237_ == 0 {
                    leanh::lean_inc(v_a_5202_);
                    v___x_5238_ = l_Lean_Exception_isRuntime(v_a_5202_);
                    v___y_5207_ = v___x_5238_;
                    state = 3;
                    continue;
                } else {
                    v___y_5207_ = v___x_5237_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_5207_ == 0 {
                    leanh::lean_del_object(v___x_5204_);
                    v_options_5208_ = leanh::lean_ctor_get(v___y_5185_, 2);
                    v_hasTrace_5209_ = leanh::lean_ctor_get_uint8(
                        v_options_5208_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5209_ == 0 {
                        leanh::lean_dec(v_a_5202_);
                        v_snd_5189_ = v_b_5180_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5210_ =
                            leanh::lean_ctor_get(v___y_5185_, 13);
                        v___x_5211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__3;
                        v___x_5212_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__6);
                        v___x_5213_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5210_,
                            v_options_5208_,
                            v___x_5212_,
                        );
                        if v___x_5213_ == 0 {
                            leanh::lean_dec(v_a_5202_);
                            v_snd_5189_ = v_b_5180_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__1);
                            leanh::lean_inc(v_a_5176_);
                            v___x_5215_ = l_Lean_MessageData_ofName(v_a_5176_);
                            v___x_5216_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5216_, 0, v___x_5214_);
                            leanh::lean_ctor_set(v___x_5216_, 1, v___x_5215_);
                            v___x_5217_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___closed__3);
                            v___x_5218_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5218_, 0, v___x_5216_);
                            leanh::lean_ctor_set(v___x_5218_, 1, v___x_5217_);
                            leanh::lean_inc(v_a_5195_);
                            v___x_5219_ = l_Lean_MessageData_ofName(v_a_5195_);
                            v___x_5220_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5220_, 0, v___x_5218_);
                            leanh::lean_ctor_set(v___x_5220_, 1, v___x_5219_);
                            v___x_5221_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8___closed__10);
                            v___x_5222_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5222_, 0, v___x_5220_);
                            leanh::lean_ctor_set(v___x_5222_, 1, v___x_5221_);
                            v___x_5223_ = l_Lean_Exception_toMessageData(v_a_5202_);
                            v___x_5224_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5224_, 0, v___x_5222_);
                            leanh::lean_ctor_set(v___x_5224_, 1, v___x_5223_);
                            v___x_5225_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v___x_5211_, v___x_5224_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_);
                            if leanh::lean_obj_tag(v___x_5225_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5225_, 1);
                                v_snd_5189_ = v_b_5180_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_5180_);
                                leanh::lean_dec(v_a_5176_);
                                v_a_5226_ = leanh::lean_ctor_get(v___x_5225_, 0);
                                v_isSharedCheck_5233_ =
                                    (!leanh::lean_is_exclusive(v___x_5225_)) as u8;
                                if v_isSharedCheck_5233_ == 0 {
                                    v___x_5228_ = v___x_5225_;
                                    v_isShared_5229_ = v_isSharedCheck_5233_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5226_);
                                    leanh::lean_dec(v___x_5225_);
                                    v___x_5228_ = leanh::lean_box(0);
                                    v_isShared_5229_ = v_isSharedCheck_5233_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_5180_);
                    leanh::lean_dec(v_a_5176_);
                    if v_isShared_5205_ == 0 {
                        v___x_5235_ = v___x_5204_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_a_5202_);
                        v___x_5235_ = v_reuseFailAlloc_5236_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5229_ == 0 {
                    v___x_5231_ = v___x_5228_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
                    v___x_5231_ = v_reuseFailAlloc_5232_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5231_;
            }
            6 => {
                return v___x_5235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3___boxed(
    mut v_a_5240_: *mut leanh::LeanObject,
    mut v_as_5241_: *mut leanh::LeanObject,
    mut v_sz_5242_: *mut leanh::LeanObject,
    mut v_i_5243_: *mut leanh::LeanObject,
    mut v_b_5244_: *mut leanh::LeanObject,
    mut v___y_5245_: *mut leanh::LeanObject,
    mut v___y_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
    mut v___y_5249_: *mut leanh::LeanObject,
    mut v___y_5250_: *mut leanh::LeanObject,
    mut v___y_5251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5252_: usize = 0;
    let mut v_i_boxed_5253_: usize = 0;
    let mut v_res_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5252_ = leanh::lean_unbox_usize(v_sz_5242_);
    leanh::lean_dec(v_sz_5242_);
    v_i_boxed_5253_ = leanh::lean_unbox_usize(v_i_5243_);
    leanh::lean_dec(v_i_5243_);
    v_res_5254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_a_5240_, v_as_5241_, v_sz_boxed_5252_, v_i_boxed_5253_, v_b_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
    leanh::lean_dec(v___y_5250_);
    leanh::lean_dec_ref(v___y_5249_);
    leanh::lean_dec(v___y_5248_);
    leanh::lean_dec_ref(v___y_5247_);
    leanh::lean_dec(v___y_5246_);
    leanh::lean_dec_ref(v___y_5245_);
    leanh::lean_dec_ref(v_as_5241_);
    return v_res_5254_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(
    mut v_simpThms_5255_: *mut leanh::LeanObject,
    mut v_as_x27_5256_: *mut leanh::LeanObject,
    mut v_b_5257_: *mut leanh::LeanObject,
    mut v___y_5258_: *mut leanh::LeanObject,
    mut v___y_5259_: *mut leanh::LeanObject,
    mut v___y_5260_: *mut leanh::LeanObject,
    mut v___y_5261_: *mut leanh::LeanObject,
    mut v___y_5262_: *mut leanh::LeanObject,
    mut v___y_5263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqThms_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5276_: usize = 0;
    let mut v___x_5277_: usize = 0;
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toUnfoldThms_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5290_: u8 = 0;
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5294_: u8 = 0;
    let mut v_val_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_5256_) == 0 {
                    v___x_5265_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5265_, 0, v_b_5257_);
                    return v___x_5265_;
                } else {
                    v_head_5266_ = leanh::lean_ctor_get(v_as_x27_5256_, 0);
                    v_tail_5267_ = leanh::lean_ctor_get(v_as_x27_5256_, 1);
                    v_toUnfoldThms_5281_ = leanh::lean_ctor_get(v_simpThms_5255_, 5);
                    v___x_5282_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_toUnfoldThms_5281_, v_head_5266_);
                    if leanh::lean_obj_tag(v___x_5282_) == 0 {
                        leanh::lean_inc(v_head_5266_);
                        v___x_5283_ = l_Lean_Meta_getEqnsFor_x3f(
                            v_head_5266_,
                            v___y_5260_,
                            v___y_5261_,
                            v___y_5262_,
                            v___y_5263_,
                        );
                        if leanh::lean_obj_tag(v___x_5283_) == 0 {
                            v_a_5284_ = leanh::lean_ctor_get(v___x_5283_, 0);
                            leanh::lean_inc(v_a_5284_);
                            leanh::lean_dec_ref_known(v___x_5283_, 1);
                            if leanh::lean_obj_tag(v_a_5284_) == 1 {
                                v_val_5285_ = leanh::lean_ctor_get(v_a_5284_, 0);
                                leanh::lean_inc(v_val_5285_);
                                leanh::lean_dec_ref_known(v_a_5284_, 1);
                                v_eqThms_5269_ = v_val_5285_;
                                v___y_5270_ = v___y_5258_;
                                v___y_5271_ = v___y_5259_;
                                v___y_5272_ = v___y_5260_;
                                v___y_5273_ = v___y_5261_;
                                v___y_5274_ = v___y_5262_;
                                v___y_5275_ = v___y_5263_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_5284_);
                                v_as_x27_5256_ = v_tail_5267_;
                                state = 0;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_5257_);
                            v_a_5287_ = leanh::lean_ctor_get(v___x_5283_, 0);
                            v_isSharedCheck_5294_ =
                                (!leanh::lean_is_exclusive(v___x_5283_)) as u8;
                            if v_isSharedCheck_5294_ == 0 {
                                v___x_5289_ = v___x_5283_;
                                v_isShared_5290_ = v_isSharedCheck_5294_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5287_);
                                leanh::lean_dec(v___x_5283_);
                                v___x_5289_ = leanh::lean_box(0);
                                v_isShared_5290_ = v_isSharedCheck_5294_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v_val_5295_ = leanh::lean_ctor_get(v___x_5282_, 0);
                        leanh::lean_inc(v_val_5295_);
                        leanh::lean_dec_ref_known(v___x_5282_, 1);
                        v_eqThms_5269_ = v_val_5295_;
                        v___y_5270_ = v___y_5258_;
                        v___y_5271_ = v___y_5259_;
                        v___y_5272_ = v___y_5260_;
                        v___y_5273_ = v___y_5261_;
                        v___y_5274_ = v___y_5262_;
                        v___y_5275_ = v___y_5263_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5276_ = lean_array_size(v_eqThms_5269_);
                v___x_5277_ = 0usize;
                leanh::lean_inc(v_head_5266_);
                v___x_5278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__3(v_head_5266_, v_eqThms_5269_, v_sz_5276_, v___x_5277_, v_b_5257_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_);
                leanh::lean_dec_ref(v_eqThms_5269_);
                if leanh::lean_obj_tag(v___x_5278_) == 0 {
                    v_a_5279_ = leanh::lean_ctor_get(v___x_5278_, 0);
                    leanh::lean_inc(v_a_5279_);
                    leanh::lean_dec_ref_known(v___x_5278_, 1);
                    v_as_x27_5256_ = v_tail_5267_;
                    v_b_5257_ = v_a_5279_;
                    state = 0;
                    continue;
                } else {
                    return v___x_5278_;
                }
            }
            2 => {
                if v_isShared_5290_ == 0 {
                    v___x_5292_ = v___x_5289_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5293_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
                    v___x_5292_ = v_reuseFailAlloc_5293_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5292_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg___boxed(
    mut v_simpThms_5296_: *mut leanh::LeanObject,
    mut v_as_x27_5297_: *mut leanh::LeanObject,
    mut v_b_5298_: *mut leanh::LeanObject,
    mut v___y_5299_: *mut leanh::LeanObject,
    mut v___y_5300_: *mut leanh::LeanObject,
    mut v___y_5301_: *mut leanh::LeanObject,
    mut v___y_5302_: *mut leanh::LeanObject,
    mut v___y_5303_: *mut leanh::LeanObject,
    mut v___y_5304_: *mut leanh::LeanObject,
    mut v___y_5305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5306_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_5296_, v_as_x27_5297_, v_b_5298_, v___y_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_);
    leanh::lean_dec(v___y_5304_);
    leanh::lean_dec_ref(v___y_5303_);
    leanh::lean_dec(v___y_5302_);
    leanh::lean_dec_ref(v___y_5301_);
    leanh::lean_dec(v___y_5300_);
    leanh::lean_dec_ref(v___y_5299_);
    leanh::lean_dec(v_as_x27_5297_);
    leanh::lean_dec_ref(v_simpThms_5296_);
    return v_res_5306_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(
    mut v_database_5316_: *mut leanh::LeanObject,
    mut v_simpThms_5317_: *mut leanh::LeanObject,
    mut v_a_5318_: *mut leanh::LeanObject,
    mut v_a_5319_: *mut leanh::LeanObject,
    mut v_a_5320_: *mut leanh::LeanObject,
    mut v_a_5321_: *mut leanh::LeanObject,
    mut v_a_5322_: *mut leanh::LeanObject,
    mut v_a_5323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_specs_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___f_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_specs_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5334_: usize = 0;
    let mut v___x_5335_: usize = 0;
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toUnfold_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5343_: usize = 0;
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5351_: u8 = 0;
    let mut v___f_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut v_a_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5364_: u8 = 0;
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5368_: u8 = 0;
    let mut v_a_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5372_: u8 = 0;
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5376_: u8 = 0;
    let mut v_a_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5384_: u8 = 0;
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_specs_5325_ = leanh::lean_ctor_get(v_database_5316_, 0);
                v_erased_5326_ = leanh::lean_ctor_get(v_database_5316_, 1);
                v_isSharedCheck_5385_ = (!leanh::lean_is_exclusive(v_database_5316_)) as u8;
                if v_isSharedCheck_5385_ == 0 {
                    v___x_5328_ = v_database_5316_;
                    v_isShared_5329_ = v_isSharedCheck_5385_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_erased_5326_);
                    leanh::lean_inc(v_specs_5325_);
                    leanh::lean_dec(v_database_5316_);
                    v___x_5328_ = leanh::lean_box(0);
                    v_isShared_5329_ = v_isSharedCheck_5385_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_5330_ =
                    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__1;
                v_specs_5331_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0_once), _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default___closed__0);
                v___x_5332_ =
                    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__2;
                v___x_5333_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_5330_, v_specs_5325_, v___x_5332_);
                leanh::lean_dec_ref(v_specs_5325_);
                v_sz_5334_ = lean_array_size(v___x_5333_);
                v___x_5335_ = 0usize;
                v___x_5336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__7(v___x_5333_, v_sz_5334_, v___x_5335_, v_specs_5331_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
                leanh::lean_dec(v___x_5333_);
                if leanh::lean_obj_tag(v___x_5336_) == 0 {
                    v_a_5337_ = leanh::lean_ctor_get(v___x_5336_, 0);
                    leanh::lean_inc(v_a_5337_);
                    leanh::lean_dec_ref_known(v___x_5336_, 1);
                    v_post_5338_ = leanh::lean_ctor_get(v_simpThms_5317_, 1);
                    v_toUnfold_5339_ = leanh::lean_ctor_get(v_simpThms_5317_, 3);
                    v_erased_5340_ = leanh::lean_ctor_get(v_simpThms_5317_, 4);
                    v___f_5341_ =
                        l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__4;
                    v___x_5342_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_5341_, v_post_5338_, v___x_5332_);
                    v_sz_5343_ = lean_array_size(v___x_5342_);
                    v___x_5344_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__8(v___x_5342_, v_sz_5343_, v___x_5335_, v_a_5337_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
                    leanh::lean_dec(v___x_5342_);
                    if leanh::lean_obj_tag(v___x_5344_) == 0 {
                        v_a_5345_ = leanh::lean_ctor_get(v___x_5344_, 0);
                        leanh::lean_inc(v_a_5345_);
                        leanh::lean_dec_ref_known(v___x_5344_, 1);
                        v___x_5346_ = l_Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9(v_toUnfold_5339_);
                        v___x_5347_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_5317_, v___x_5346_, v_a_5345_, v_a_5318_, v_a_5319_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_);
                        leanh::lean_dec(v___x_5346_);
                        if leanh::lean_obj_tag(v___x_5347_) == 0 {
                            v_a_5348_ = leanh::lean_ctor_get(v___x_5347_, 0);
                            v_isSharedCheck_5360_ =
                                (!leanh::lean_is_exclusive(v___x_5347_)) as u8;
                            if v_isSharedCheck_5360_ == 0 {
                                v___x_5350_ = v___x_5347_;
                                v_isShared_5351_ = v_isSharedCheck_5360_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5348_);
                                leanh::lean_dec(v___x_5347_);
                                v___x_5350_ = leanh::lean_box(0);
                                v_isShared_5351_ = v_isSharedCheck_5360_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_5328_);
                            leanh::lean_dec_ref(v_erased_5326_);
                            v_a_5361_ = leanh::lean_ctor_get(v___x_5347_, 0);
                            v_isSharedCheck_5368_ =
                                (!leanh::lean_is_exclusive(v___x_5347_)) as u8;
                            if v_isSharedCheck_5368_ == 0 {
                                v___x_5363_ = v___x_5347_;
                                v_isShared_5364_ = v_isSharedCheck_5368_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5361_);
                                leanh::lean_dec(v___x_5347_);
                                v___x_5363_ = leanh::lean_box(0);
                                v_isShared_5364_ = v_isSharedCheck_5368_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_5328_);
                        leanh::lean_dec_ref(v_erased_5326_);
                        v_a_5369_ = leanh::lean_ctor_get(v___x_5344_, 0);
                        v_isSharedCheck_5376_ =
                            (!leanh::lean_is_exclusive(v___x_5344_)) as u8;
                        if v_isSharedCheck_5376_ == 0 {
                            v___x_5371_ = v___x_5344_;
                            v_isShared_5372_ = v_isSharedCheck_5376_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5369_);
                            leanh::lean_dec(v___x_5344_);
                            v___x_5371_ = leanh::lean_box(0);
                            v_isShared_5372_ = v_isSharedCheck_5376_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5328_);
                    leanh::lean_dec_ref(v_erased_5326_);
                    v_a_5377_ = leanh::lean_ctor_get(v___x_5336_, 0);
                    v_isSharedCheck_5384_ = (!leanh::lean_is_exclusive(v___x_5336_)) as u8;
                    if v_isSharedCheck_5384_ == 0 {
                        v___x_5379_ = v___x_5336_;
                        v_isShared_5380_ = v_isSharedCheck_5384_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5377_);
                        leanh::lean_dec(v___x_5336_);
                        v___x_5379_ = leanh::lean_box(0);
                        v_isShared_5380_ = v_isSharedCheck_5384_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___f_5352_ =
                    l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___closed__5;
                v_erased_5353_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v___f_5352_, v_erased_5340_, v_erased_5326_);
                if v_isShared_5329_ == 0 {
                    leanh::lean_ctor_set(v___x_5328_, 1, v_erased_5353_);
                    leanh::lean_ctor_set(v___x_5328_, 0, v_a_5348_);
                    v___x_5355_ = v___x_5328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 1, v_erased_5353_);
                    v___x_5355_ = v_reuseFailAlloc_5359_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5351_ == 0 {
                    leanh::lean_ctor_set(v___x_5350_, 0, v___x_5355_);
                    v___x_5357_ = v___x_5350_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5358_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5358_, 0, v___x_5355_);
                    v___x_5357_ = v_reuseFailAlloc_5358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5357_;
            }
            5 => {
                if v_isShared_5364_ == 0 {
                    v___x_5366_ = v___x_5363_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5367_, 0, v_a_5361_);
                    v___x_5366_ = v_reuseFailAlloc_5367_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5366_;
            }
            7 => {
                if v_isShared_5372_ == 0 {
                    v___x_5374_ = v___x_5371_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5375_, 0, v_a_5369_);
                    v___x_5374_ = v_reuseFailAlloc_5375_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5374_;
            }
            9 => {
                if v_isShared_5380_ == 0 {
                    v___x_5382_ = v___x_5379_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
                    v___x_5382_ = v_reuseFailAlloc_5383_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(
    mut v_database_5386_: *mut leanh::LeanObject,
    mut v_simpThms_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
    mut v_a_5389_: *mut leanh::LeanObject,
    mut v_a_5390_: *mut leanh::LeanObject,
    mut v_a_5391_: *mut leanh::LeanObject,
    mut v_a_5392_: *mut leanh::LeanObject,
    mut v_a_5393_: *mut leanh::LeanObject,
    mut v_a_5394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5395_ = l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase(
        v_database_5386_,
        v_simpThms_5387_,
        v_a_5388_,
        v_a_5389_,
        v_a_5390_,
        v_a_5391_,
        v_a_5392_,
        v_a_5393_,
    );
    leanh::lean_dec(v_a_5393_);
    leanh::lean_dec_ref(v_a_5392_);
    leanh::lean_dec(v_a_5391_);
    leanh::lean_dec_ref(v_a_5390_);
    leanh::lean_dec(v_a_5389_);
    leanh::lean_dec_ref(v_a_5388_);
    leanh::lean_dec_ref(v_simpThms_5387_);
    return v_res_5395_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0(
    mut v_00_u03b2_5396_: *mut leanh::LeanObject,
    mut v_x_5397_: *mut leanh::LeanObject,
    mut v_x_5398_: *mut leanh::LeanObject,
    mut v_x_5399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5400_ = l_Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0___redArg(v_x_5397_, v_x_5398_, v_x_5399_);
    return v___x_5400_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(
    mut v_cls_5401_: *mut leanh::LeanObject,
    mut v_msg_5402_: *mut leanh::LeanObject,
    mut v___y_5403_: *mut leanh::LeanObject,
    mut v___y_5404_: *mut leanh::LeanObject,
    mut v___y_5405_: *mut leanh::LeanObject,
    mut v___y_5406_: *mut leanh::LeanObject,
    mut v___y_5407_: *mut leanh::LeanObject,
    mut v___y_5408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5410_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___redArg(v_cls_5401_, v_msg_5402_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_);
    return v___x_5410_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2___boxed(
    mut v_cls_5411_: *mut leanh::LeanObject,
    mut v_msg_5412_: *mut leanh::LeanObject,
    mut v___y_5413_: *mut leanh::LeanObject,
    mut v___y_5414_: *mut leanh::LeanObject,
    mut v___y_5415_: *mut leanh::LeanObject,
    mut v___y_5416_: *mut leanh::LeanObject,
    mut v___y_5417_: *mut leanh::LeanObject,
    mut v___y_5418_: *mut leanh::LeanObject,
    mut v___y_5419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5420_ =
        l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__2(
            v_cls_5411_,
            v_msg_5412_,
            v___y_5413_,
            v___y_5414_,
            v___y_5415_,
            v___y_5416_,
            v___y_5417_,
            v___y_5418_,
        );
    leanh::lean_dec(v___y_5418_);
    leanh::lean_dec_ref(v___y_5417_);
    leanh::lean_dec(v___y_5416_);
    leanh::lean_dec_ref(v___y_5415_);
    leanh::lean_dec(v___y_5414_);
    leanh::lean_dec_ref(v___y_5413_);
    return v_res_5420_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(
    mut v_00_u03b2_5421_: *mut leanh::LeanObject,
    mut v_x_5422_: *mut leanh::LeanObject,
    mut v_x_5423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5424_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___redArg(v_x_5422_, v_x_5423_);
    return v___x_5424_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4___boxed(
    mut v_00_u03b2_5425_: *mut leanh::LeanObject,
    mut v_x_5426_: *mut leanh::LeanObject,
    mut v_x_5427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5428_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4(v_00_u03b2_5425_, v_x_5426_, v_x_5427_);
    leanh::lean_dec(v_x_5427_);
    leanh::lean_dec_ref(v_x_5426_);
    return v_res_5428_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(
    mut v_00_u03c3_5429_: *mut leanh::LeanObject,
    mut v_00_u03b1_5430_: *mut leanh::LeanObject,
    mut v_f_5431_: *mut leanh::LeanObject,
    mut v_x_5432_: *mut leanh::LeanObject,
    mut v_x_5433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5434_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___redArg(v_f_5431_, v_x_5432_, v_x_5433_);
    return v___x_5434_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5___boxed(
    mut v_00_u03c3_5435_: *mut leanh::LeanObject,
    mut v_00_u03b1_5436_: *mut leanh::LeanObject,
    mut v_f_5437_: *mut leanh::LeanObject,
    mut v_x_5438_: *mut leanh::LeanObject,
    mut v_x_5439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5440_ = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5(v_00_u03c3_5435_, v_00_u03b1_5436_, v_f_5437_, v_x_5438_, v_x_5439_);
    leanh::lean_dec_ref(v_x_5439_);
    return v_res_5440_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(
    mut v_map_5441_: *mut leanh::LeanObject,
    mut v_f_5442_: *mut leanh::LeanObject,
    mut v_init_5443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5444_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_5442_, v_map_5441_, v_init_5443_);
    return v___x_5444_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg___boxed(
    mut v_map_5445_: *mut leanh::LeanObject,
    mut v_f_5446_: *mut leanh::LeanObject,
    mut v_init_5447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5448_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___redArg(v_map_5445_, v_f_5446_, v_init_5447_);
    leanh::lean_dec_ref(v_map_5445_);
    return v_res_5448_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(
    mut v_00_u03c3_5449_: *mut leanh::LeanObject,
    mut v_00_u03b2_5450_: *mut leanh::LeanObject,
    mut v_map_5451_: *mut leanh::LeanObject,
    mut v_f_5452_: *mut leanh::LeanObject,
    mut v_init_5453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5454_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_5452_, v_map_5451_, v_init_5453_);
    return v___x_5454_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6___boxed(
    mut v_00_u03c3_5455_: *mut leanh::LeanObject,
    mut v_00_u03b2_5456_: *mut leanh::LeanObject,
    mut v_map_5457_: *mut leanh::LeanObject,
    mut v_f_5458_: *mut leanh::LeanObject,
    mut v_init_5459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5460_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6(v_00_u03c3_5455_, v_00_u03b2_5456_, v_map_5457_, v_f_5458_, v_init_5459_);
    leanh::lean_dec_ref(v_map_5457_);
    return v_res_5460_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(
    mut v_simpThms_5461_: *mut leanh::LeanObject,
    mut v_as_5462_: *mut leanh::LeanObject,
    mut v_as_x27_5463_: *mut leanh::LeanObject,
    mut v_b_5464_: *mut leanh::LeanObject,
    mut v_a_5465_: *mut leanh::LeanObject,
    mut v___y_5466_: *mut leanh::LeanObject,
    mut v___y_5467_: *mut leanh::LeanObject,
    mut v___y_5468_: *mut leanh::LeanObject,
    mut v___y_5469_: *mut leanh::LeanObject,
    mut v___y_5470_: *mut leanh::LeanObject,
    mut v___y_5471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5473_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___redArg(v_simpThms_5461_, v_as_x27_5463_, v_b_5464_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_, v___y_5471_);
    return v___x_5473_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10___boxed(
    mut v_simpThms_5474_: *mut leanh::LeanObject,
    mut v_as_5475_: *mut leanh::LeanObject,
    mut v_as_x27_5476_: *mut leanh::LeanObject,
    mut v_b_5477_: *mut leanh::LeanObject,
    mut v_a_5478_: *mut leanh::LeanObject,
    mut v___y_5479_: *mut leanh::LeanObject,
    mut v___y_5480_: *mut leanh::LeanObject,
    mut v___y_5481_: *mut leanh::LeanObject,
    mut v___y_5482_: *mut leanh::LeanObject,
    mut v___y_5483_: *mut leanh::LeanObject,
    mut v___y_5484_: *mut leanh::LeanObject,
    mut v___y_5485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5486_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__10(v_simpThms_5474_, v_as_5475_, v_as_x27_5476_, v_b_5477_, v_a_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
    leanh::lean_dec(v___y_5484_);
    leanh::lean_dec_ref(v___y_5483_);
    leanh::lean_dec(v___y_5482_);
    leanh::lean_dec_ref(v___y_5481_);
    leanh::lean_dec(v___y_5480_);
    leanh::lean_dec_ref(v___y_5479_);
    leanh::lean_dec(v_as_x27_5476_);
    leanh::lean_dec(v_as_5475_);
    leanh::lean_dec_ref(v_simpThms_5474_);
    return v_res_5486_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg(
    mut v_map_5487_: *mut leanh::LeanObject,
    mut v_f_5488_: *mut leanh::LeanObject,
    mut v_init_5489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5490_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_5488_, v_map_5487_, v_init_5489_);
    return v___x_5490_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg___boxed(
    mut v_map_5491_: *mut leanh::LeanObject,
    mut v_f_5492_: *mut leanh::LeanObject,
    mut v_init_5493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5494_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___redArg(v_map_5491_, v_f_5492_, v_init_5493_);
    leanh::lean_dec_ref(v_map_5491_);
    return v_res_5494_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11(
    mut v_00_u03c3_5495_: *mut leanh::LeanObject,
    mut v_00_u03b2_5496_: *mut leanh::LeanObject,
    mut v_map_5497_: *mut leanh::LeanObject,
    mut v_f_5498_: *mut leanh::LeanObject,
    mut v_init_5499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5500_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_5498_, v_map_5497_, v_init_5499_);
    return v___x_5500_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11___boxed(
    mut v_00_u03c3_5501_: *mut leanh::LeanObject,
    mut v_00_u03b2_5502_: *mut leanh::LeanObject,
    mut v_map_5503_: *mut leanh::LeanObject,
    mut v_f_5504_: *mut leanh::LeanObject,
    mut v_init_5505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5506_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__11(v_00_u03c3_5501_, v_00_u03b2_5502_, v_map_5503_, v_f_5504_, v_init_5505_);
    leanh::lean_dec_ref(v_map_5503_);
    return v_res_5506_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(
    mut v_00_u03b2_5507_: *mut leanh::LeanObject,
    mut v_x_5508_: *mut leanh::LeanObject,
    mut v_x_5509_: usize,
    mut v_x_5510_: usize,
    mut v_x_5511_: *mut leanh::LeanObject,
    mut v_x_5512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg(v_x_5508_, v_x_5509_, v_x_5510_, v_x_5511_, v_x_5512_);
    return v___x_5513_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___boxed(
    mut v_00_u03b2_5514_: *mut leanh::LeanObject,
    mut v_x_5515_: *mut leanh::LeanObject,
    mut v_x_5516_: *mut leanh::LeanObject,
    mut v_x_5517_: *mut leanh::LeanObject,
    mut v_x_5518_: *mut leanh::LeanObject,
    mut v_x_5519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_28508__boxed_5520_: usize = 0;
    let mut v_x_28509__boxed_5521_: usize = 0;
    let mut v_res_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_28508__boxed_5520_ = leanh::lean_unbox_usize(v_x_5516_);
    leanh::lean_dec(v_x_5516_);
    v_x_28509__boxed_5521_ = leanh::lean_unbox_usize(v_x_5517_);
    leanh::lean_dec(v_x_5517_);
    v_res_5522_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0(v_00_u03b2_5514_, v_x_5515_, v_x_28508__boxed_5520_, v_x_28509__boxed_5521_, v_x_5518_, v_x_5519_);
    return v_res_5522_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(
    mut v_00_u03b2_5523_: *mut leanh::LeanObject,
    mut v_x_5524_: *mut leanh::LeanObject,
    mut v_x_5525_: usize,
    mut v_x_5526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___redArg(v_x_5524_, v_x_5525_, v_x_5526_);
    return v___x_5527_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6___boxed(
    mut v_00_u03b2_5528_: *mut leanh::LeanObject,
    mut v_x_5529_: *mut leanh::LeanObject,
    mut v_x_5530_: *mut leanh::LeanObject,
    mut v_x_5531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_28525__boxed_5532_: usize = 0;
    let mut v_res_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_28525__boxed_5532_ = leanh::lean_unbox_usize(v_x_5530_);
    leanh::lean_dec(v_x_5530_);
    v_res_5533_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6(v_00_u03b2_5528_, v_x_5529_, v_x_28525__boxed_5532_, v_x_5531_);
    leanh::lean_dec(v_x_5531_);
    leanh::lean_dec_ref(v_x_5529_);
    return v_res_5533_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(
    mut v_00_u03b1_5534_: *mut leanh::LeanObject,
    mut v_00_u03c3_5535_: *mut leanh::LeanObject,
    mut v_f_5536_: *mut leanh::LeanObject,
    mut v_as_5537_: *mut leanh::LeanObject,
    mut v_i_5538_: usize,
    mut v_stop_5539_: usize,
    mut v_b_5540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___redArg(v_f_5536_, v_as_5537_, v_i_5538_, v_stop_5539_, v_b_5540_);
    return v___x_5541_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8___boxed(
    mut v_00_u03b1_5542_: *mut leanh::LeanObject,
    mut v_00_u03c3_5543_: *mut leanh::LeanObject,
    mut v_f_5544_: *mut leanh::LeanObject,
    mut v_as_5545_: *mut leanh::LeanObject,
    mut v_i_5546_: *mut leanh::LeanObject,
    mut v_stop_5547_: *mut leanh::LeanObject,
    mut v_b_5548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5549_: usize = 0;
    let mut v_stop_boxed_5550_: usize = 0;
    let mut v_res_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5549_ = leanh::lean_unbox_usize(v_i_5546_);
    leanh::lean_dec(v_i_5546_);
    v_stop_boxed_5550_ = leanh::lean_unbox_usize(v_stop_5547_);
    leanh::lean_dec(v_stop_5547_);
    v_res_5551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__8(v_00_u03b1_5542_, v_00_u03c3_5543_, v_f_5544_, v_as_5545_, v_i_boxed_5549_, v_stop_boxed_5550_, v_b_5548_);
    leanh::lean_dec_ref(v_as_5545_);
    return v_res_5551_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(
    mut v_00_u03b1_5552_: *mut leanh::LeanObject,
    mut v_00_u03c3_5553_: *mut leanh::LeanObject,
    mut v_f_5554_: *mut leanh::LeanObject,
    mut v_as_5555_: *mut leanh::LeanObject,
    mut v_i_5556_: usize,
    mut v_stop_5557_: usize,
    mut v_b_5558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5559_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___redArg(v_f_5554_, v_as_5555_, v_i_5556_, v_stop_5557_, v_b_5558_);
    return v___x_5559_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9___boxed(
    mut v_00_u03b1_5560_: *mut leanh::LeanObject,
    mut v_00_u03c3_5561_: *mut leanh::LeanObject,
    mut v_f_5562_: *mut leanh::LeanObject,
    mut v_as_5563_: *mut leanh::LeanObject,
    mut v_i_5564_: *mut leanh::LeanObject,
    mut v_stop_5565_: *mut leanh::LeanObject,
    mut v_b_5566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5567_: usize = 0;
    let mut v_stop_boxed_5568_: usize = 0;
    let mut v_res_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5567_ = leanh::lean_unbox_usize(v_i_5564_);
    leanh::lean_dec(v_i_5564_);
    v_stop_boxed_5568_ = leanh::lean_unbox_usize(v_stop_5565_);
    leanh::lean_dec(v_stop_5565_);
    v_res_5569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_DiscrTree_Trie_foldValuesM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__5_spec__9(v_00_u03b1_5560_, v_00_u03c3_5561_, v_f_5562_, v_as_5563_, v_i_boxed_5567_, v_stop_boxed_5568_, v_b_5566_);
    leanh::lean_dec_ref(v_as_5563_);
    return v_res_5569_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(
    mut v_00_u03c3_5570_: *mut leanh::LeanObject,
    mut v_00_u03b1_5571_: *mut leanh::LeanObject,
    mut v_00_u03b2_5572_: *mut leanh::LeanObject,
    mut v_f_5573_: *mut leanh::LeanObject,
    mut v_x_5574_: *mut leanh::LeanObject,
    mut v_x_5575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5576_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_5573_, v_x_5574_, v_x_5575_);
    return v___x_5576_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___boxed(
    mut v_00_u03c3_5577_: *mut leanh::LeanObject,
    mut v_00_u03b1_5578_: *mut leanh::LeanObject,
    mut v_00_u03b2_5579_: *mut leanh::LeanObject,
    mut v_f_5580_: *mut leanh::LeanObject,
    mut v_x_5581_: *mut leanh::LeanObject,
    mut v_x_5582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11(v_00_u03c3_5577_, v_00_u03b1_5578_, v_00_u03b2_5579_, v_f_5580_, v_x_5581_, v_x_5582_);
    leanh::lean_dec_ref(v_x_5581_);
    return v_res_5583_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(
    mut v_00_u03b2_5584_: *mut leanh::LeanObject,
    mut v_m_5585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5586_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___redArg(v_m_5585_);
    return v___x_5586_;
}
pub unsafe fn l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15___boxed(
    mut v_00_u03b2_5587_: *mut leanh::LeanObject,
    mut v_m_5588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5589_ = l_Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15(v_00_u03b2_5587_, v_m_5588_);
    leanh::lean_dec_ref(v_m_5588_);
    return v_res_5589_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5590_: *mut leanh::LeanObject,
    mut v_n_5591_: *mut leanh::LeanObject,
    mut v_k_5592_: *mut leanh::LeanObject,
    mut v_v_5593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5594_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1___redArg(v_n_5591_, v_k_5592_, v_v_5593_);
    return v___x_5594_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5595_: *mut leanh::LeanObject,
    mut v_depth_5596_: usize,
    mut v_keys_5597_: *mut leanh::LeanObject,
    mut v_vals_5598_: *mut leanh::LeanObject,
    mut v_heq_5599_: *mut leanh::LeanObject,
    mut v_i_5600_: *mut leanh::LeanObject,
    mut v_entries_5601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg(v_depth_5596_, v_keys_5597_, v_vals_5598_, v_i_5600_, v_entries_5601_);
    return v___x_5602_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5603_: *mut leanh::LeanObject,
    mut v_depth_5604_: *mut leanh::LeanObject,
    mut v_keys_5605_: *mut leanh::LeanObject,
    mut v_vals_5606_: *mut leanh::LeanObject,
    mut v_heq_5607_: *mut leanh::LeanObject,
    mut v_i_5608_: *mut leanh::LeanObject,
    mut v_entries_5609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5610_: usize = 0;
    let mut v_res_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5610_ = leanh::lean_unbox_usize(v_depth_5604_);
    leanh::lean_dec(v_depth_5604_);
    v_res_5611_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2(v_00_u03b2_5603_, v_depth_boxed_5610_, v_keys_5605_, v_vals_5606_, v_heq_5607_, v_i_5608_, v_entries_5609_);
    leanh::lean_dec_ref(v_vals_5606_);
    leanh::lean_dec_ref(v_keys_5605_);
    return v_res_5611_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(
    mut v_00_u03b2_5612_: *mut leanh::LeanObject,
    mut v_x_5613_: *mut leanh::LeanObject,
    mut v_x_5614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5615_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___redArg(v_x_5613_, v_x_5614_);
    return v___x_5615_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_5616_: *mut leanh::LeanObject,
    mut v_x_5617_: *mut leanh::LeanObject,
    mut v_x_5618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5619_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5(v_00_u03b2_5616_, v_x_5617_, v_x_5618_);
    leanh::lean_dec(v_x_5618_);
    leanh::lean_dec_ref(v_x_5617_);
    return v_res_5619_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6(
    mut v_00_u03b2_5620_: *mut leanh::LeanObject,
    mut v_x_5621_: *mut leanh::LeanObject,
    mut v_x_5622_: *mut leanh::LeanObject,
    mut v_x_5623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5624_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6___redArg(v_x_5621_, v_x_5622_, v_x_5623_);
    return v___x_5624_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13(
    mut v_00_u03b2_5625_: *mut leanh::LeanObject,
    mut v_keys_5626_: *mut leanh::LeanObject,
    mut v_vals_5627_: *mut leanh::LeanObject,
    mut v_heq_5628_: *mut leanh::LeanObject,
    mut v_i_5629_: *mut leanh::LeanObject,
    mut v_k_5630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5631_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___redArg(v_keys_5626_, v_vals_5627_, v_i_5629_, v_k_5630_);
    return v___x_5631_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13___boxed(
    mut v_00_u03b2_5632_: *mut leanh::LeanObject,
    mut v_keys_5633_: *mut leanh::LeanObject,
    mut v_vals_5634_: *mut leanh::LeanObject,
    mut v_heq_5635_: *mut leanh::LeanObject,
    mut v_i_5636_: *mut leanh::LeanObject,
    mut v_k_5637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5638_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__4_spec__6_spec__13(v_00_u03b2_5632_, v_keys_5633_, v_vals_5634_, v_heq_5635_, v_i_5636_, v_k_5637_);
    leanh::lean_dec(v_k_5637_);
    leanh::lean_dec_ref(v_vals_5634_);
    leanh::lean_dec_ref(v_keys_5633_);
    return v_res_5638_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(
    mut v_00_u03b1_5639_: *mut leanh::LeanObject,
    mut v_00_u03b2_5640_: *mut leanh::LeanObject,
    mut v_00_u03c3_5641_: *mut leanh::LeanObject,
    mut v_f_5642_: *mut leanh::LeanObject,
    mut v_as_5643_: *mut leanh::LeanObject,
    mut v_i_5644_: usize,
    mut v_stop_5645_: usize,
    mut v_b_5646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___redArg(v_f_5642_, v_as_5643_, v_i_5644_, v_stop_5645_, v_b_5646_);
    return v___x_5647_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19___boxed(
    mut v_00_u03b1_5648_: *mut leanh::LeanObject,
    mut v_00_u03b2_5649_: *mut leanh::LeanObject,
    mut v_00_u03c3_5650_: *mut leanh::LeanObject,
    mut v_f_5651_: *mut leanh::LeanObject,
    mut v_as_5652_: *mut leanh::LeanObject,
    mut v_i_5653_: *mut leanh::LeanObject,
    mut v_stop_5654_: *mut leanh::LeanObject,
    mut v_b_5655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5656_: usize = 0;
    let mut v_stop_boxed_5657_: usize = 0;
    let mut v_res_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5656_ = leanh::lean_unbox_usize(v_i_5653_);
    leanh::lean_dec(v_i_5653_);
    v_stop_boxed_5657_ = leanh::lean_unbox_usize(v_stop_5654_);
    leanh::lean_dec(v_stop_5654_);
    v_res_5658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__19(v_00_u03b1_5648_, v_00_u03b2_5649_, v_00_u03c3_5650_, v_f_5651_, v_as_5652_, v_i_boxed_5656_, v_stop_boxed_5657_, v_b_5655_);
    leanh::lean_dec_ref(v_as_5652_);
    return v_res_5658_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20(
    mut v_00_u03c3_5659_: *mut leanh::LeanObject,
    mut v_00_u03b1_5660_: *mut leanh::LeanObject,
    mut v_00_u03b2_5661_: *mut leanh::LeanObject,
    mut v_f_5662_: *mut leanh::LeanObject,
    mut v_keys_5663_: *mut leanh::LeanObject,
    mut v_vals_5664_: *mut leanh::LeanObject,
    mut v_heq_5665_: *mut leanh::LeanObject,
    mut v_i_5666_: *mut leanh::LeanObject,
    mut v_acc_5667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5668_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___redArg(v_f_5662_, v_keys_5663_, v_vals_5664_, v_i_5666_, v_acc_5667_);
    return v___x_5668_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20___boxed(
    mut v_00_u03c3_5669_: *mut leanh::LeanObject,
    mut v_00_u03b1_5670_: *mut leanh::LeanObject,
    mut v_00_u03b2_5671_: *mut leanh::LeanObject,
    mut v_f_5672_: *mut leanh::LeanObject,
    mut v_keys_5673_: *mut leanh::LeanObject,
    mut v_vals_5674_: *mut leanh::LeanObject,
    mut v_heq_5675_: *mut leanh::LeanObject,
    mut v_i_5676_: *mut leanh::LeanObject,
    mut v_acc_5677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5678_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11_spec__20(v_00_u03c3_5669_, v_00_u03b1_5670_, v_00_u03b2_5671_, v_f_5672_, v_keys_5673_, v_vals_5674_, v_heq_5675_, v_i_5676_, v_acc_5677_);
    leanh::lean_dec_ref(v_vals_5674_);
    leanh::lean_dec_ref(v_keys_5673_);
    return v_res_5678_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25(
    mut v_00_u03c3_5679_: *mut leanh::LeanObject,
    mut v_00_u03b2_5680_: *mut leanh::LeanObject,
    mut v_map_5681_: *mut leanh::LeanObject,
    mut v_f_5682_: *mut leanh::LeanObject,
    mut v_init_5683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5684_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___redArg(v_map_5681_, v_f_5682_, v_init_5683_);
    return v___x_5684_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25___boxed(
    mut v_00_u03c3_5685_: *mut leanh::LeanObject,
    mut v_00_u03b2_5686_: *mut leanh::LeanObject,
    mut v_map_5687_: *mut leanh::LeanObject,
    mut v_f_5688_: *mut leanh::LeanObject,
    mut v_init_5689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5690_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25(v_00_u03c3_5685_, v_00_u03b2_5686_, v_map_5687_, v_f_5688_, v_init_5689_);
    leanh::lean_dec_ref(v_map_5687_);
    return v_res_5690_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13(
    mut v_00_u03b2_5691_: *mut leanh::LeanObject,
    mut v_x_5692_: *mut leanh::LeanObject,
    mut v_x_5693_: *mut leanh::LeanObject,
    mut v_x_5694_: *mut leanh::LeanObject,
    mut v_x_5695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5696_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__1_spec__13___redArg(v_x_5692_, v_x_5693_, v_x_5694_, v_x_5695_);
    return v___x_5696_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(
    mut v_00_u03b2_5697_: *mut leanh::LeanObject,
    mut v_x_5698_: *mut leanh::LeanObject,
    mut v_x_5699_: usize,
    mut v_x_5700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5701_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___redArg(v_x_5698_, v_x_5699_, v_x_5700_);
    return v___x_5701_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17___boxed(
    mut v_00_u03b2_5702_: *mut leanh::LeanObject,
    mut v_x_5703_: *mut leanh::LeanObject,
    mut v_x_5704_: *mut leanh::LeanObject,
    mut v_x_5705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_28588__boxed_5706_: usize = 0;
    let mut v_res_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_28588__boxed_5706_ = leanh::lean_unbox_usize(v_x_5704_);
    leanh::lean_dec(v_x_5704_);
    v_res_5707_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17(v_00_u03b2_5702_, v_x_5703_, v_x_28588__boxed_5706_, v_x_5705_);
    leanh::lean_dec(v_x_5705_);
    leanh::lean_dec_ref(v_x_5703_);
    return v_res_5707_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19(
    mut v_00_u03b2_5708_: *mut leanh::LeanObject,
    mut v_x_5709_: *mut leanh::LeanObject,
    mut v_x_5710_: usize,
    mut v_x_5711_: usize,
    mut v_x_5712_: *mut leanh::LeanObject,
    mut v_x_5713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5714_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___redArg(v_x_5709_, v_x_5710_, v_x_5711_, v_x_5712_, v_x_5713_);
    return v___x_5714_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19___boxed(
    mut v_00_u03b2_5715_: *mut leanh::LeanObject,
    mut v_x_5716_: *mut leanh::LeanObject,
    mut v_x_5717_: *mut leanh::LeanObject,
    mut v_x_5718_: *mut leanh::LeanObject,
    mut v_x_5719_: *mut leanh::LeanObject,
    mut v_x_5720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_28599__boxed_5721_: usize = 0;
    let mut v_x_28600__boxed_5722_: usize = 0;
    let mut v_res_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_28599__boxed_5721_ = leanh::lean_unbox_usize(v_x_5717_);
    leanh::lean_dec(v_x_5717_);
    v_x_28600__boxed_5722_ = leanh::lean_unbox_usize(v_x_5718_);
    leanh::lean_dec(v_x_5718_);
    v_res_5723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19(v_00_u03b2_5715_, v_x_5716_, v_x_28599__boxed_5721_, v_x_28600__boxed_5722_, v_x_5719_, v_x_5720_);
    return v_res_5723_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg(
    mut v_map_5724_: *mut leanh::LeanObject,
    mut v_f_5725_: *mut leanh::LeanObject,
    mut v_init_5726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5727_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_5725_, v_map_5724_, v_init_5726_);
    return v___x_5727_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg___boxed(
    mut v_map_5728_: *mut leanh::LeanObject,
    mut v_f_5729_: *mut leanh::LeanObject,
    mut v_init_5730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5731_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___redArg(v_map_5728_, v_f_5729_, v_init_5730_);
    leanh::lean_dec_ref(v_map_5728_);
    return v_res_5731_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33(
    mut v_00_u03c3_5732_: *mut leanh::LeanObject,
    mut v_00_u03b2_5733_: *mut leanh::LeanObject,
    mut v_map_5734_: *mut leanh::LeanObject,
    mut v_f_5735_: *mut leanh::LeanObject,
    mut v_init_5736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5737_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__6_spec__11___redArg(v_f_5735_, v_map_5734_, v_init_5736_);
    return v___x_5737_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33___boxed(
    mut v_00_u03c3_5738_: *mut leanh::LeanObject,
    mut v_00_u03b2_5739_: *mut leanh::LeanObject,
    mut v_map_5740_: *mut leanh::LeanObject,
    mut v_f_5741_: *mut leanh::LeanObject,
    mut v_init_5742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5743_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toList___at___00Lean_PersistentHashSet_toList___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__9_spec__15_spec__25_spec__33(v_00_u03c3_5738_, v_00_u03b2_5739_, v_map_5740_, v_f_5741_, v_init_5742_);
    leanh::lean_dec_ref(v_map_5740_);
    return v_res_5743_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(
    mut v_00_u03b2_5744_: *mut leanh::LeanObject,
    mut v_keys_5745_: *mut leanh::LeanObject,
    mut v_vals_5746_: *mut leanh::LeanObject,
    mut v_heq_5747_: *mut leanh::LeanObject,
    mut v_i_5748_: *mut leanh::LeanObject,
    mut v_k_5749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___redArg(v_keys_5745_, v_vals_5746_, v_i_5748_, v_k_5749_);
    return v___x_5750_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25___boxed(
    mut v_00_u03b2_5751_: *mut leanh::LeanObject,
    mut v_keys_5752_: *mut leanh::LeanObject,
    mut v_vals_5753_: *mut leanh::LeanObject,
    mut v_heq_5754_: *mut leanh::LeanObject,
    mut v_i_5755_: *mut leanh::LeanObject,
    mut v_k_5756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5757_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__5_spec__17_spec__25(v_00_u03b2_5751_, v_keys_5752_, v_vals_5753_, v_heq_5754_, v_i_5755_, v_k_5756_);
    leanh::lean_dec(v_k_5756_);
    leanh::lean_dec_ref(v_vals_5753_);
    leanh::lean_dec_ref(v_keys_5752_);
    return v_res_5757_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28(
    mut v_00_u03b2_5758_: *mut leanh::LeanObject,
    mut v_n_5759_: *mut leanh::LeanObject,
    mut v_k_5760_: *mut leanh::LeanObject,
    mut v_v_5761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5762_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28___redArg(v_n_5759_, v_k_5760_, v_v_5761_);
    return v___x_5762_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29(
    mut v_00_u03b2_5763_: *mut leanh::LeanObject,
    mut v_depth_5764_: usize,
    mut v_keys_5765_: *mut leanh::LeanObject,
    mut v_vals_5766_: *mut leanh::LeanObject,
    mut v_heq_5767_: *mut leanh::LeanObject,
    mut v_i_5768_: *mut leanh::LeanObject,
    mut v_entries_5769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5770_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___redArg(v_depth_5764_, v_keys_5765_, v_vals_5766_, v_i_5768_, v_entries_5769_);
    return v___x_5770_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29___boxed(
    mut v_00_u03b2_5771_: *mut leanh::LeanObject,
    mut v_depth_5772_: *mut leanh::LeanObject,
    mut v_keys_5773_: *mut leanh::LeanObject,
    mut v_vals_5774_: *mut leanh::LeanObject,
    mut v_heq_5775_: *mut leanh::LeanObject,
    mut v_i_5776_: *mut leanh::LeanObject,
    mut v_entries_5777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5778_: usize = 0;
    let mut v_res_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5778_ = leanh::lean_unbox_usize(v_depth_5772_);
    leanh::lean_dec(v_depth_5772_);
    v_res_5779_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__29(v_00_u03b2_5771_, v_depth_boxed_5778_, v_keys_5773_, v_vals_5774_, v_heq_5775_, v_i_5776_, v_entries_5777_);
    leanh::lean_dec_ref(v_vals_5774_);
    leanh::lean_dec_ref(v_keys_5773_);
    return v_res_5779_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34(
    mut v_x_5780_: *mut leanh::LeanObject,
    mut v_keys_5781_: *mut leanh::LeanObject,
    mut v_v_5782_: *mut leanh::LeanObject,
    mut v_k_5783_: *mut leanh::LeanObject,
    mut v_as_5784_: *mut leanh::LeanObject,
    mut v_k_5785_: *mut leanh::LeanObject,
    mut v_x_5786_: *mut leanh::LeanObject,
    mut v_x_5787_: *mut leanh::LeanObject,
    mut v_x_5788_: *mut leanh::LeanObject,
    mut v_x_5789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5790_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___redArg(v_x_5780_, v_keys_5781_, v_v_5782_, v_k_5783_, v_as_5784_, v_k_5785_, v_x_5786_, v_x_5787_);
    return v___x_5790_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34___boxed(
    mut v_x_5791_: *mut leanh::LeanObject,
    mut v_keys_5792_: *mut leanh::LeanObject,
    mut v_v_5793_: *mut leanh::LeanObject,
    mut v_k_5794_: *mut leanh::LeanObject,
    mut v_as_5795_: *mut leanh::LeanObject,
    mut v_k_5796_: *mut leanh::LeanObject,
    mut v_x_5797_: *mut leanh::LeanObject,
    mut v_x_5798_: *mut leanh::LeanObject,
    mut v_x_5799_: *mut leanh::LeanObject,
    mut v_x_5800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5801_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7_spec__22_spec__34(v_x_5791_, v_keys_5792_, v_v_5793_, v_k_5794_, v_as_5795_, v_k_5796_, v_x_5797_, v_x_5798_, v_x_5799_, v_x_5800_);
    leanh::lean_dec_ref(v_k_5796_);
    leanh::lean_dec_ref(v_keys_5792_);
    leanh::lean_dec(v_x_5791_);
    return v_res_5801_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34(
    mut v_00_u03b2_5802_: *mut leanh::LeanObject,
    mut v_x_5803_: *mut leanh::LeanObject,
    mut v_x_5804_: *mut leanh::LeanObject,
    mut v_x_5805_: *mut leanh::LeanObject,
    mut v_x_5806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5807_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__6_spec__19_spec__28_spec__34___redArg(v_x_5803_, v_x_5804_, v_x_5805_, v_x_5806_);
    return v___x_5807_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(
    mut v_xs_5808_: *mut leanh::LeanObject,
    mut v_j_5809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5811_: u8 = 0;
    let mut v_one_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_priority_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: u8 = 0;
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5810_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5811_ = lean_nat_dec_eq(v_j_5809_, v_zero_5810_);
                if v_isZero_5811_ == 1 {
                    leanh::lean_dec(v_j_5809_);
                    return v_xs_5808_;
                } else {
                    v_one_5812_ = leanh::lean_unsigned_to_nat(1);
                    v_n_5813_ = lean_nat_sub(v_j_5809_, v_one_5812_);
                    v___x_5814_ = lean_array_fget_borrowed(v_xs_5808_, v_n_5813_);
                    v_priority_5815_ = leanh::lean_ctor_get(v___x_5814_, 3);
                    v___x_5816_ = lean_array_fget_borrowed(v_xs_5808_, v_j_5809_);
                    v_priority_5817_ = leanh::lean_ctor_get(v___x_5816_, 3);
                    v___x_5818_ = lean_nat_dec_lt(v_priority_5815_, v_priority_5817_);
                    if v___x_5818_ == 0 {
                        leanh::lean_dec(v_n_5813_);
                        leanh::lean_dec(v_j_5809_);
                        return v_xs_5808_;
                    } else {
                        v___x_5819_ = lean_array_fswap(v_xs_5808_, v_j_5809_, v_n_5813_);
                        leanh::lean_dec(v_j_5809_);
                        v_xs_5808_ = v___x_5819_;
                        v_j_5809_ = v_n_5813_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(
    mut v_xs_5821_: *mut leanh::LeanObject,
    mut v_i_5822_: *mut leanh::LeanObject,
    mut v_fuel_5823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5825_: u8 = 0;
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: u8 = 0;
    let mut v_one_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5824_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5825_ = lean_nat_dec_eq(v_fuel_5823_, v_zero_5824_);
                if v_isZero_5825_ == 1 {
                    leanh::lean_dec(v_fuel_5823_);
                    leanh::lean_dec(v_i_5822_);
                    return v_xs_5821_;
                } else {
                    v___x_5826_ = lean_array_get_size(v_xs_5821_);
                    v___x_5827_ = lean_nat_dec_lt(v_i_5822_, v___x_5826_);
                    if v___x_5827_ == 0 {
                        leanh::lean_dec(v_fuel_5823_);
                        leanh::lean_dec(v_i_5822_);
                        return v_xs_5821_;
                    } else {
                        v_one_5828_ = leanh::lean_unsigned_to_nat(1);
                        v_n_5829_ = lean_nat_sub(v_fuel_5823_, v_one_5828_);
                        leanh::lean_dec(v_fuel_5823_);
                        leanh::lean_inc(v_i_5822_);
                        v___x_5830_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(v_xs_5821_, v_i_5822_);
                        v___x_5831_ = lean_nat_add(v_i_5822_, v_one_5828_);
                        leanh::lean_dec(v_i_5822_);
                        v_xs_5821_ = v___x_5830_;
                        v_i_5822_ = v___x_5831_;
                        v_fuel_5823_ = v_n_5829_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(
    mut v_keys_5833_: *mut leanh::LeanObject,
    mut v_i_5834_: *mut leanh::LeanObject,
    mut v_k_5835_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: u8 = 0;
    let mut v_k_x27_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: u8 = 0;
    let mut v___x_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5836_ = lean_array_get_size(v_keys_5833_);
                v___x_5837_ = lean_nat_dec_lt(v_i_5834_, v___x_5836_);
                if v___x_5837_ == 0 {
                    leanh::lean_dec_ref(v_k_5835_);
                    leanh::lean_dec(v_i_5834_);
                    return v___x_5837_;
                } else {
                    v_k_x27_5838_ = lean_array_fget_borrowed(v_keys_5833_, v_i_5834_);
                    leanh::lean_inc(v_k_x27_5838_);
                    leanh::lean_inc_ref(v_k_5835_);
                    v___x_5839_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                        v_k_5835_,
                        v_k_x27_5838_,
                    );
                    if v___x_5839_ == 0 {
                        v___x_5840_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5841_ = lean_nat_add(v_i_5834_, v___x_5840_);
                        leanh::lean_dec(v_i_5834_);
                        v_i_5834_ = v___x_5841_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_5835_);
                        leanh::lean_dec(v_i_5834_);
                        return v___x_5839_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_5843_: *mut leanh::LeanObject,
    mut v_i_5844_: *mut leanh::LeanObject,
    mut v_k_5845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5846_: u8 = 0;
    let mut v_r_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5846_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_keys_5843_, v_i_5844_, v_k_5845_);
    leanh::lean_dec_ref(v_keys_5843_);
    v_r_5847_ = leanh::lean_box((v_res_5846_) as usize);
    return v_r_5847_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(
    mut v_x_5848_: *mut leanh::LeanObject,
    mut v_x_5849_: usize,
    mut v_x_5850_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: usize = 0;
    let mut v___x_5854_: usize = 0;
    let mut v___x_5855_: usize = 0;
    let mut v_j_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: u8 = 0;
    let mut v_node_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5861_: usize = 0;
    let mut v___x_5863_: u8 = 0;
    let mut v_ks_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5848_) == 0 {
                    v_es_5851_ = leanh::lean_ctor_get(v_x_5848_, 0);
                    leanh::lean_inc_ref(v_es_5851_);
                    leanh::lean_dec_ref_known(v_x_5848_, 1);
                    v___x_5852_ = leanh::lean_box(2);
                    v___x_5853_ = 5usize;
                    v___x_5854_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0___redArg___closed__1);
                    v___x_5855_ = lean_usize_land(v_x_5849_, v___x_5854_);
                    v_j_5856_ = lean_usize_to_nat(v___x_5855_);
                    v___x_5857_ = lean_array_get(v___x_5852_, v_es_5851_, v_j_5856_);
                    leanh::lean_dec(v_j_5856_);
                    leanh::lean_dec_ref(v_es_5851_);
                    match leanh::lean_obj_tag(v___x_5857_) {
                        0 => {
                            v_key_5858_ = leanh::lean_ctor_get(v___x_5857_, 0);
                            leanh::lean_inc(v_key_5858_);
                            leanh::lean_dec_ref_known(v___x_5857_, 2);
                            v___x_5859_ = l_Lean_Elab_Tactic_Do_SpecAttr_instBEqSpecProof_beq(
                                v_x_5850_,
                                v_key_5858_,
                            );
                            return v___x_5859_;
                        }
                        1 => {
                            v_node_5860_ = leanh::lean_ctor_get(v___x_5857_, 0);
                            leanh::lean_inc(v_node_5860_);
                            leanh::lean_dec_ref_known(v___x_5857_, 1);
                            v___x_5861_ = lean_usize_shift_right(v_x_5849_, v___x_5853_);
                            v_x_5848_ = v_node_5860_;
                            v_x_5849_ = v___x_5861_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_x_5850_);
                            v___x_5863_ = 0;
                            return v___x_5863_;
                        }
                    }
                } else {
                    v_ks_5864_ = leanh::lean_ctor_get(v_x_5848_, 0);
                    leanh::lean_inc_ref(v_ks_5864_);
                    leanh::lean_dec_ref_known(v_x_5848_, 2);
                    v___x_5865_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5866_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_ks_5864_, v___x_5865_, v_x_5850_);
                    leanh::lean_dec_ref(v_ks_5864_);
                    return v___x_5866_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg___boxed(
    mut v_x_5867_: *mut leanh::LeanObject,
    mut v_x_5868_: *mut leanh::LeanObject,
    mut v_x_5869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4073__boxed_5870_: usize = 0;
    let mut v_res_5871_: u8 = 0;
    let mut v_r_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4073__boxed_5870_ = leanh::lean_unbox_usize(v_x_5868_);
    leanh::lean_dec(v_x_5868_);
    v_res_5871_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_5867_, v_x_4073__boxed_5870_, v_x_5869_);
    v_r_5872_ = leanh::lean_box((v_res_5871_) as usize);
    return v_r_5872_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(
    mut v_x_5873_: *mut leanh::LeanObject,
    mut v_x_5874_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_5876_: u64 = 0;
    let mut v___x_5877_: usize = 0;
    let mut v___x_5878_: u8 = 0;
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: u64 = 0;
    let mut v_hash_5881_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5879_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecProof_key(v_x_5874_);
                if leanh::lean_obj_tag(v___x_5879_) == 0 {
                    v___x_5880_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_5876_ = v___x_5880_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5881_ = leanh::lean_ctor_get_uint64(
                        v___x_5879_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec(v___x_5879_);
                    v___y_5876_ = v_hash_5881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5877_ = lean_uint64_to_usize(v___y_5876_);
                v___x_5878_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_5873_, v___x_5877_, v_x_5874_);
                return v___x_5878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg___boxed(
    mut v_x_5882_: *mut leanh::LeanObject,
    mut v_x_5883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5884_: u8 = 0;
    let mut v_r_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5884_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_x_5882_, v_x_5883_);
    v_r_5885_ = leanh::lean_box((v_res_5884_) as usize);
    return v_r_5885_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(
    mut v_database_5886_: *mut leanh::LeanObject,
    mut v_as_5887_: *mut leanh::LeanObject,
    mut v_i_5888_: usize,
    mut v_stop_5889_: usize,
    mut v_b_5890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: usize = 0;
    let mut v___x_5894_: usize = 0;
    let mut v___x_5896_: u8 = 0;
    let mut v_erased_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: u8 = 0;
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5896_ = lean_usize_dec_eq(v_i_5888_, v_stop_5889_);
                if v___x_5896_ == 0 {
                    v_erased_5897_ = leanh::lean_ctor_get(v_database_5886_, 1);
                    v___x_5898_ = lean_array_uget_borrowed(v_as_5887_, v_i_5888_);
                    v_proof_5899_ = leanh::lean_ctor_get(v___x_5898_, 1);
                    leanh::lean_inc_ref(v_proof_5899_);
                    leanh::lean_inc_ref(v_erased_5897_);
                    v___x_5900_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_erased_5897_, v_proof_5899_);
                    if v___x_5900_ == 0 {
                        leanh::lean_inc(v___x_5898_);
                        v___x_5901_ = lean_array_push(v_b_5890_, v___x_5898_);
                        v___y_5892_ = v___x_5901_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5892_ = v_b_5890_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_database_5886_);
                    return v_b_5890_;
                }
            }
            1 => {
                v___x_5893_ = 1usize;
                v___x_5894_ = lean_usize_add(v_i_5888_, v___x_5893_);
                v_i_5888_ = v___x_5894_;
                v_b_5890_ = v___y_5892_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3___boxed(
    mut v_database_5902_: *mut leanh::LeanObject,
    mut v_as_5903_: *mut leanh::LeanObject,
    mut v_i_5904_: *mut leanh::LeanObject,
    mut v_stop_5905_: *mut leanh::LeanObject,
    mut v_b_5906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5907_: usize = 0;
    let mut v_stop_boxed_5908_: usize = 0;
    let mut v_res_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5907_ = leanh::lean_unbox_usize(v_i_5904_);
    leanh::lean_dec(v_i_5904_);
    v_stop_boxed_5908_ = leanh::lean_unbox_usize(v_stop_5905_);
    leanh::lean_dec(v_stop_5905_);
    v_res_5909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_5902_, v_as_5903_, v_i_boxed_5907_, v_stop_boxed_5908_, v_b_5906_);
    leanh::lean_dec_ref(v_as_5903_);
    return v_res_5909_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(
    mut v_a_5913_: *mut leanh::LeanObject,
    mut v_as_5914_: *mut leanh::LeanObject,
    mut v_sz_5915_: usize,
    mut v_i_5916_: usize,
    mut v_b_5917_: *mut leanh::LeanObject,
    mut v___y_5918_: *mut leanh::LeanObject,
    mut v___y_5919_: *mut leanh::LeanObject,
    mut v___y_5920_: *mut leanh::LeanObject,
    mut v___y_5921_: *mut leanh::LeanObject,
    mut v___y_5922_: *mut leanh::LeanObject,
    mut v___y_5923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5925_: u8 = 0;
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5933_: u8 = 0;
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5937_: u8 = 0;
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5946_: u8 = 0;
    let mut v_unused_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: usize = 0;
    let mut v___x_5950_: usize = 0;
    let mut v_isSharedCheck_5952_: u8 = 0;
    let mut v_a_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5956_: u8 = 0;
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5925_ = lean_usize_dec_lt(v_i_5916_, v_sz_5915_);
                if v___x_5925_ == 0 {
                    leanh::lean_dec_ref(v_a_5913_);
                    v___x_5926_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5926_, 0, v_b_5917_);
                    return v___x_5926_;
                } else {
                    leanh::lean_dec_ref(v_b_5917_);
                    v_a_5927_ = lean_array_uget_borrowed(v_as_5914_, v_i_5916_);
                    v_pattern_5928_ = leanh::lean_ctor_get(v_a_5927_, 0);
                    leanh::lean_inc_ref(v_a_5913_);
                    leanh::lean_inc_ref(v_pattern_5928_);
                    v___x_5929_ = l_Lean_Meta_Sym_Pattern_match_x3f(
                        v_pattern_5928_,
                        v_a_5913_,
                        v___x_5925_,
                        v___y_5918_,
                        v___y_5919_,
                        v___y_5920_,
                        v___y_5921_,
                        v___y_5922_,
                        v___y_5923_,
                    );
                    if leanh::lean_obj_tag(v___x_5929_) == 0 {
                        v_a_5930_ = leanh::lean_ctor_get(v___x_5929_, 0);
                        v_isSharedCheck_5952_ =
                            (!leanh::lean_is_exclusive(v___x_5929_)) as u8;
                        if v_isSharedCheck_5952_ == 0 {
                            v___x_5932_ = v___x_5929_;
                            v_isShared_5933_ = v_isSharedCheck_5952_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5930_);
                            leanh::lean_dec(v___x_5929_);
                            v___x_5932_ = leanh::lean_box(0);
                            v_isShared_5933_ = v_isSharedCheck_5952_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_5913_);
                        v_a_5953_ = leanh::lean_ctor_get(v___x_5929_, 0);
                        v_isSharedCheck_5960_ =
                            (!leanh::lean_is_exclusive(v___x_5929_)) as u8;
                        if v_isSharedCheck_5960_ == 0 {
                            v___x_5955_ = v___x_5929_;
                            v_isShared_5956_ = v_isSharedCheck_5960_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5953_);
                            leanh::lean_dec(v___x_5929_);
                            v___x_5955_ = leanh::lean_box(0);
                            v_isShared_5956_ = v_isSharedCheck_5960_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5934_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v_a_5930_) == 1 {
                    leanh::lean_dec_ref(v_a_5913_);
                    v_isSharedCheck_5946_ = (!leanh::lean_is_exclusive(v_a_5930_)) as u8;
                    if v_isSharedCheck_5946_ == 0 {
                        v_unused_5947_ = leanh::lean_ctor_get(v_a_5930_, 0);
                        leanh::lean_dec(v_unused_5947_);
                        v___x_5936_ = v_a_5930_;
                        v_isShared_5937_ = v_isSharedCheck_5946_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_5930_);
                        v___x_5936_ = leanh::lean_box(0);
                        v_isShared_5937_ = v_isSharedCheck_5946_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5932_);
                    leanh::lean_dec(v_a_5930_);
                    v___x_5948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0;
                    v___x_5949_ = 1usize;
                    v___x_5950_ = lean_usize_add(v_i_5916_, v___x_5949_);
                    v_i_5916_ = v___x_5950_;
                    v_b_5917_ = v___x_5948_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_a_5927_);
                v___x_5938_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5938_, 0, v_a_5927_);
                if v_isShared_5937_ == 0 {
                    leanh::lean_ctor_set(v___x_5936_, 0, v___x_5938_);
                    v___x_5940_ = v___x_5936_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5945_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5945_, 0, v___x_5938_);
                    v___x_5940_ = v_reuseFailAlloc_5945_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5941_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5941_, 0, v___x_5940_);
                leanh::lean_ctor_set(v___x_5941_, 1, v___x_5934_);
                if v_isShared_5933_ == 0 {
                    leanh::lean_ctor_set(v___x_5932_, 0, v___x_5941_);
                    v___x_5943_ = v___x_5932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 0, v___x_5941_);
                    v___x_5943_ = v_reuseFailAlloc_5944_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5943_;
            }
            5 => {
                if v_isShared_5956_ == 0 {
                    v___x_5958_ = v___x_5955_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5959_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5959_, 0, v_a_5953_);
                    v___x_5958_ = v_reuseFailAlloc_5959_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___boxed(
    mut v_a_5961_: *mut leanh::LeanObject,
    mut v_as_5962_: *mut leanh::LeanObject,
    mut v_sz_5963_: *mut leanh::LeanObject,
    mut v_i_5964_: *mut leanh::LeanObject,
    mut v_b_5965_: *mut leanh::LeanObject,
    mut v___y_5966_: *mut leanh::LeanObject,
    mut v___y_5967_: *mut leanh::LeanObject,
    mut v___y_5968_: *mut leanh::LeanObject,
    mut v___y_5969_: *mut leanh::LeanObject,
    mut v___y_5970_: *mut leanh::LeanObject,
    mut v___y_5971_: *mut leanh::LeanObject,
    mut v___y_5972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5973_: usize = 0;
    let mut v_i_boxed_5974_: usize = 0;
    let mut v_res_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5973_ = leanh::lean_unbox_usize(v_sz_5963_);
    leanh::lean_dec(v_sz_5963_);
    v_i_boxed_5974_ = leanh::lean_unbox_usize(v_i_5964_);
    leanh::lean_dec(v_i_5964_);
    v_res_5975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(v_a_5961_, v_as_5962_, v_sz_boxed_5973_, v_i_boxed_5974_, v_b_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_);
    leanh::lean_dec(v___y_5971_);
    leanh::lean_dec_ref(v___y_5970_);
    leanh::lean_dec(v___y_5969_);
    leanh::lean_dec_ref(v___y_5968_);
    leanh::lean_dec(v___y_5967_);
    leanh::lean_dec_ref(v___y_5966_);
    leanh::lean_dec_ref(v_as_5962_);
    return v_res_5975_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(
    mut v_database_5976_: *mut leanh::LeanObject,
    mut v_e_5977_: *mut leanh::LeanObject,
    mut v_a_5978_: *mut leanh::LeanObject,
    mut v_a_5979_: *mut leanh::LeanObject,
    mut v_a_5980_: *mut leanh::LeanObject,
    mut v_a_5981_: *mut leanh::LeanObject,
    mut v_a_5982_: *mut leanh::LeanObject,
    mut v_a_5983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5989_: u8 = 0;
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5994_: u8 = 0;
    let mut v_specs_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: u8 = 0;
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6005_: usize = 0;
    let mut v___x_6006_: usize = 0;
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6011_: u8 = 0;
    let mut v_fst_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut v_a_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6027_: u8 = 0;
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut v___x_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: u8 = 0;
    let mut v___x_6042_: u8 = 0;
    let mut v___x_6043_: usize = 0;
    let mut v___x_6044_: usize = 0;
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: usize = 0;
    let mut v___x_6047_: usize = 0;
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6049_: u8 = 0;
    let mut v_a_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6053_: u8 = 0;
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6057_: u8 = 0;
    let mut v_isSharedCheck_6058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5985_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremNew_spec__0___redArg(v_e_5977_, v_a_5981_);
                v_a_5986_ = leanh::lean_ctor_get(v___x_5985_, 0);
                v_isSharedCheck_6058_ = (!leanh::lean_is_exclusive(v___x_5985_)) as u8;
                if v_isSharedCheck_6058_ == 0 {
                    v___x_5988_ = v___x_5985_;
                    v_isShared_5989_ = v_isSharedCheck_6058_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5986_);
                    leanh::lean_dec(v___x_5985_);
                    v___x_5988_ = leanh::lean_box(0);
                    v_isShared_5989_ = v_isSharedCheck_6058_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5990_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_5986_, v_a_5979_);
                if leanh::lean_obj_tag(v___x_5990_) == 0 {
                    v_a_5991_ = leanh::lean_ctor_get(v___x_5990_, 0);
                    v_isSharedCheck_6049_ = (!leanh::lean_is_exclusive(v___x_5990_)) as u8;
                    if v_isSharedCheck_6049_ == 0 {
                        v___x_5993_ = v___x_5990_;
                        v_isShared_5994_ = v_isSharedCheck_6049_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5991_);
                        leanh::lean_dec(v___x_5990_);
                        v___x_5993_ = leanh::lean_box(0);
                        v_isShared_5994_ = v_isSharedCheck_6049_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5988_);
                    leanh::lean_dec_ref(v_database_5976_);
                    v_a_6050_ = leanh::lean_ctor_get(v___x_5990_, 0);
                    v_isSharedCheck_6057_ = (!leanh::lean_is_exclusive(v___x_5990_)) as u8;
                    if v_isSharedCheck_6057_ == 0 {
                        v___x_6052_ = v___x_5990_;
                        v_isShared_6053_ = v_isSharedCheck_6057_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6050_);
                        leanh::lean_dec(v___x_5990_);
                        v___x_6052_ = leanh::lean_box(0);
                        v_isShared_6053_ = v_isSharedCheck_6057_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_specs_5995_ = leanh::lean_ctor_get(v_database_5976_, 0);
                v___x_5996_ = l_Lean_Meta_Sym_getMatch___redArg(v_specs_5995_, v_a_5991_);
                v___x_5997_ = leanh::lean_unsigned_to_nat(0);
                v___x_6039_ = lean_array_get_size(v___x_5996_);
                v___x_6040_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Sym_insertPattern___at___00Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase_spec__1_spec__2_spec__7___closed__0;
                v___x_6041_ = lean_nat_dec_lt(v___x_5997_, v___x_6039_);
                if v___x_6041_ == 0 {
                    leanh::lean_dec_ref(v___x_5996_);
                    leanh::lean_dec_ref(v_database_5976_);
                    v___y_5999_ = v___x_6040_;
                    state = 3;
                    continue;
                } else {
                    v___x_6042_ = lean_nat_dec_le(v___x_6039_, v___x_6039_);
                    if v___x_6042_ == 0 {
                        if v___x_6041_ == 0 {
                            leanh::lean_dec_ref(v___x_5996_);
                            leanh::lean_dec_ref(v_database_5976_);
                            v___y_5999_ = v___x_6040_;
                            state = 3;
                            continue;
                        } else {
                            v___x_6043_ = 0usize;
                            v___x_6044_ = lean_usize_of_nat(v___x_6039_);
                            v___x_6045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_5976_, v___x_5996_, v___x_6043_, v___x_6044_, v___x_6040_);
                            leanh::lean_dec_ref(v___x_5996_);
                            v___y_5999_ = v___x_6045_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_6046_ = 0usize;
                        v___x_6047_ = lean_usize_of_nat(v___x_6039_);
                        v___x_6048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__3(v_database_5976_, v___x_5996_, v___x_6046_, v___x_6047_, v___x_6040_);
                        leanh::lean_dec_ref(v___x_5996_);
                        v___y_5999_ = v___x_6048_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6000_ = lean_array_get_size(v___y_5999_);
                v___x_6001_ = leanh::lean_unsigned_to_nat(1);
                v___x_6002_ = lean_nat_dec_eq(v___x_6000_, v___x_6001_);
                if v___x_6002_ == 0 {
                    leanh::lean_del_object(v___x_5993_);
                    v___x_6003_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1(v___y_5999_, v___x_5997_, v___x_6000_);
                    v___x_6004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2___closed__0;
                    v_sz_6005_ = lean_array_size(v___x_6003_);
                    v___x_6006_ = 0usize;
                    v___x_6007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__2(v_a_5991_, v___x_6003_, v_sz_6005_, v___x_6006_, v___x_6004_, v_a_5978_, v_a_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_);
                    if leanh::lean_obj_tag(v___x_6007_) == 0 {
                        v_a_6008_ = leanh::lean_ctor_get(v___x_6007_, 0);
                        v_isSharedCheck_6023_ =
                            (!leanh::lean_is_exclusive(v___x_6007_)) as u8;
                        if v_isSharedCheck_6023_ == 0 {
                            v___x_6010_ = v___x_6007_;
                            v_isShared_6011_ = v_isSharedCheck_6023_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6008_);
                            leanh::lean_dec(v___x_6007_);
                            v___x_6010_ = leanh::lean_box(0);
                            v_isShared_6011_ = v_isSharedCheck_6023_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_6003_);
                        leanh::lean_del_object(v___x_5988_);
                        v_a_6024_ = leanh::lean_ctor_get(v___x_6007_, 0);
                        v_isSharedCheck_6031_ =
                            (!leanh::lean_is_exclusive(v___x_6007_)) as u8;
                        if v_isSharedCheck_6031_ == 0 {
                            v___x_6026_ = v___x_6007_;
                            v_isShared_6027_ = v_isSharedCheck_6031_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6024_);
                            leanh::lean_dec(v___x_6007_);
                            v___x_6026_ = leanh::lean_box(0);
                            v_isShared_6027_ = v_isSharedCheck_6031_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5991_);
                    v___x_6032_ = lean_array_fget(v___y_5999_, v___x_5997_);
                    leanh::lean_dec_ref(v___y_5999_);
                    if v_isShared_5989_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5988_, 1);
                        leanh::lean_ctor_set(v___x_5988_, 0, v___x_6032_);
                        v___x_6034_ = v___x_5988_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6038_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6038_, 0, v___x_6032_);
                        v___x_6034_ = v_reuseFailAlloc_6038_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_6012_ = leanh::lean_ctor_get(v_a_6008_, 0);
                leanh::lean_inc(v_fst_6012_);
                leanh::lean_dec(v_a_6008_);
                if leanh::lean_obj_tag(v_fst_6012_) == 0 {
                    if v_isShared_5989_ == 0 {
                        leanh::lean_ctor_set(v___x_5988_, 0, v___x_6003_);
                        v___x_6014_ = v___x_5988_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6018_, 0, v___x_6003_);
                        v___x_6014_ = v_reuseFailAlloc_6018_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6003_);
                    leanh::lean_del_object(v___x_5988_);
                    v_val_6019_ = leanh::lean_ctor_get(v_fst_6012_, 0);
                    leanh::lean_inc(v_val_6019_);
                    leanh::lean_dec_ref_known(v_fst_6012_, 1);
                    if v_isShared_6011_ == 0 {
                        leanh::lean_ctor_set(v___x_6010_, 0, v_val_6019_);
                        v___x_6021_ = v___x_6010_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6022_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v_val_6019_);
                        v___x_6021_ = v_reuseFailAlloc_6022_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6011_ == 0 {
                    leanh::lean_ctor_set(v___x_6010_, 0, v___x_6014_);
                    v___x_6016_ = v___x_6010_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6017_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6017_, 0, v___x_6014_);
                    v___x_6016_ = v_reuseFailAlloc_6017_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6016_;
            }
            7 => {
                return v___x_6021_;
            }
            8 => {
                if v_isShared_6027_ == 0 {
                    v___x_6029_ = v___x_6026_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6030_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
                    v___x_6029_ = v_reuseFailAlloc_6030_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6029_;
            }
            10 => {
                if v_isShared_5994_ == 0 {
                    leanh::lean_ctor_set(v___x_5993_, 0, v___x_6034_);
                    v___x_6036_ = v___x_5993_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6037_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6034_);
                    v___x_6036_ = v_reuseFailAlloc_6037_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6036_;
            }
            12 => {
                if v_isShared_6053_ == 0 {
                    v___x_6055_ = v___x_6052_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6056_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
                    v___x_6055_ = v_reuseFailAlloc_6056_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs___boxed(
    mut v_database_6059_: *mut leanh::LeanObject,
    mut v_e_6060_: *mut leanh::LeanObject,
    mut v_a_6061_: *mut leanh::LeanObject,
    mut v_a_6062_: *mut leanh::LeanObject,
    mut v_a_6063_: *mut leanh::LeanObject,
    mut v_a_6064_: *mut leanh::LeanObject,
    mut v_a_6065_: *mut leanh::LeanObject,
    mut v_a_6066_: *mut leanh::LeanObject,
    mut v_a_6067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6068_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs(
        v_database_6059_,
        v_e_6060_,
        v_a_6061_,
        v_a_6062_,
        v_a_6063_,
        v_a_6064_,
        v_a_6065_,
        v_a_6066_,
    );
    leanh::lean_dec(v_a_6066_);
    leanh::lean_dec_ref(v_a_6065_);
    leanh::lean_dec(v_a_6064_);
    leanh::lean_dec_ref(v_a_6063_);
    leanh::lean_dec(v_a_6062_);
    leanh::lean_dec_ref(v_a_6061_);
    return v_res_6068_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(
    mut v_00_u03b2_6069_: *mut leanh::LeanObject,
    mut v_x_6070_: *mut leanh::LeanObject,
    mut v_x_6071_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6072_: u8 = 0;
    v___x_6072_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___redArg(v_x_6070_, v_x_6071_);
    return v___x_6072_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0___boxed(
    mut v_00_u03b2_6073_: *mut leanh::LeanObject,
    mut v_x_6074_: *mut leanh::LeanObject,
    mut v_x_6075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6076_: u8 = 0;
    let mut v_r_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6076_ = l_Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0(v_00_u03b2_6073_, v_x_6074_, v_x_6075_);
    v_r_6077_ = leanh::lean_box((v_res_6076_) as usize);
    return v_r_6077_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(
    mut v_00_u03b2_6078_: *mut leanh::LeanObject,
    mut v_x_6079_: *mut leanh::LeanObject,
    mut v_x_6080_: usize,
    mut v_x_6081_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6082_: u8 = 0;
    v___x_6082_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___redArg(v_x_6079_, v_x_6080_, v_x_6081_);
    return v___x_6082_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0___boxed(
    mut v_00_u03b2_6083_: *mut leanh::LeanObject,
    mut v_x_6084_: *mut leanh::LeanObject,
    mut v_x_6085_: *mut leanh::LeanObject,
    mut v_x_6086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4418__boxed_6087_: usize = 0;
    let mut v_res_6088_: u8 = 0;
    let mut v_r_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4418__boxed_6087_ = leanh::lean_unbox_usize(v_x_6085_);
    leanh::lean_dec(v_x_6085_);
    v_res_6088_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0(v_00_u03b2_6083_, v_x_6084_, v_x_4418__boxed_6087_, v_x_6086_);
    v_r_6089_ = leanh::lean_box((v_res_6088_) as usize);
    return v_r_6089_;
}
pub unsafe fn l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2(
    mut v_xs_6090_: *mut leanh::LeanObject,
    mut v_j_6091_: *mut leanh::LeanObject,
    mut v_h_6092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6093_ = l___private_Init_Data_Array_InsertionSort_0__Array_insertionSort_swapLoop___at___00__private_Init_Data_Array_InsertionSort_0__Array_insertionSort_traverse___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__1_spec__2___redArg(v_xs_6090_, v_j_6091_);
    return v___x_6093_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1(
    mut v_00_u03b2_6094_: *mut leanh::LeanObject,
    mut v_keys_6095_: *mut leanh::LeanObject,
    mut v_vals_6096_: *mut leanh::LeanObject,
    mut v_heq_6097_: *mut leanh::LeanObject,
    mut v_i_6098_: *mut leanh::LeanObject,
    mut v_k_6099_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6100_: u8 = 0;
    v___x_6100_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___redArg(v_keys_6095_, v_i_6098_, v_k_6099_);
    return v___x_6100_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_6101_: *mut leanh::LeanObject,
    mut v_keys_6102_: *mut leanh::LeanObject,
    mut v_vals_6103_: *mut leanh::LeanObject,
    mut v_heq_6104_: *mut leanh::LeanObject,
    mut v_i_6105_: *mut leanh::LeanObject,
    mut v_k_6106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6107_: u8 = 0;
    let mut v_r_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6107_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Elab_Tactic_Do_SpecAttr_SpecTheoremsNew_findSpecs_spec__0_spec__0_spec__1(v_00_u03b2_6101_, v_keys_6102_, v_vals_6103_, v_heq_6104_, v_i_6105_, v_k_6106_);
    leanh::lean_dec_ref(v_vals_6103_);
    leanh::lean_dec_ref(v_keys_6102_);
    v_r_6108_ = leanh::lean_box((v_res_6107_) as usize);
    return v_r_6108_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default();
    leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew_default,
    );
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremNew);
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default();
    leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew_default,
    );
    l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew =
        _init_l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_SpecAttr_instInhabitedSpecTheoremsNew);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_Attr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_DiscrTree_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
}