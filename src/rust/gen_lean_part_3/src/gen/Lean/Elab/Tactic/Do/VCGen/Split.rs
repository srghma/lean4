// Lean compiler output
// Module: Lean.Elab.Tactic.Do.VCGen.Split
// Imports: Lean.Meta.Tactic.Simp.Types Lean.Meta.Match.MatcherApp.Transform Lean.Data.Array Lean.Meta.Match.Rewrite Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Assumption
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_set, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_instantiate_rev, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::Basic::l_instMonadControlTOfPure___redArg;
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map, l_Array_append___redArg,
    l_Array_mapFinIdxM_map___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_replaceRef, l_List_lengthTR___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_pure___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AuxRecursor::l_Lean_isCasesOnRecursor;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_Core_mkFreshUserName, l_Lean_mkArrow,
};
use crate::r#gen::Lean::Data::Array::{
    initialize_Lean_Data_Array, l_Array_mask___redArg, runtime_initialize_Lean_Data_Array,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numCtors;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_const___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isApp, l_Lean_Expr_isAppOf, l_Lean_Expr_isFVar___boxed,
    l_Lean_Expr_looseBVarRange, l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
    l_Lean_mkApp5, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkNot, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Expr_abstractM___boxed, l_Lean_Meta_etaExpand___boxed, l_Lean_Meta_inferType___boxed,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_lambdaTelescope___redArg, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_mkLambdaFVars___boxed, l_Lean_Meta_withLocalDecl___redArg,
    l_Lean_Meta_withLocalDeclD___redArg, l_Lean_Meta_withLocalDeclsDND___redArg,
};
use crate::r#gen::Lean::Meta::InferType::{
    l_Lean_Meta_getLevel___boxed, l_Lean_Meta_inferArgumentTypesN___boxed,
};
use crate::r#gen::Lean::Meta::Match::MatcherApp::Basic::{
    l_Lean_Meta_MatcherApp_altNumParams, l_Lean_Meta_MatcherApp_toExpr,
};
use crate::r#gen::Lean::Meta::Match::MatcherApp::Transform::{
    initialize_Lean_Meta_Match_MatcherApp_Transform, l_Lean_Meta_MatcherApp_transform___redArg,
    runtime_initialize_Lean_Meta_Match_MatcherApp_Transform,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_Extension_getMatcherInfo_x3f, l_Lean_Meta_Match_MatcherInfo_arity,
    l_Lean_Meta_Match_MatcherInfo_getMotivePos, l_Lean_Meta_Match_MatcherInfo_numAlts,
    l_Lean_Meta_Match_instInhabitedAltParamInfo_default,
};
use crate::r#gen::Lean::Meta::Match::Rewrite::{
    initialize_Lean_Meta_Match_Rewrite, l_Lean_Meta_rwIfWith, l_Lean_Meta_rwMatcher,
    runtime_initialize_Lean_Meta_Match_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, l_Lean_Meta_findLocalDeclWithType_x3f,
    runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Rewrite::{
    initialize_Lean_Meta_Tactic_Simp_Rewrite, l_Lean_Meta_Simp_simpMatchDiscrs_x3f,
    runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    initialize_Lean_Meta_Tactic_Simp_Types, runtime_initialize_Lean_Meta_Tactic_Simp_Types,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value:
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
    m_data: [105, 116, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        18356704233129443855 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value:
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
    m_data: [101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value
        ) as *mut leanh::LeanObject,
        18388690793488095770 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value:
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
    m_data: [116, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        3844805874353431675 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value:
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
    m_data: [100, 101, 99, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value
        ) as *mut leanh::LeanObject,
        13886804137793424261 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value:
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
    m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value
        ) as *mut leanh::LeanObject,
        4342836574150310743 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value:
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
    m_data: [100, 105, 116, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value
        ) as *mut leanh::LeanObject,
        8391571994004792969 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value:
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
    m_data: [97, 108, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value
        ) as *mut leanh::LeanObject,
        6207155323350122738 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value:
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
    m_data: [100, 105, 115, 99, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value
        ) as *mut leanh::LeanObject,
        11893266011724725697 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value:
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
    m_fun: l_Lean_Meta_etaExpand___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value:
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
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value:
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
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value:
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
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value:
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
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value:
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
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value:
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
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value:
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
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value:
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
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value:
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
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value:
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
    m_data: [99, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value)
            as *mut leanh::LeanObject,
        388469914488256294 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value:
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
    m_fun: l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value:
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
    m_data: [105, 115, 70, 97, 108, 115, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value
        ) as *mut leanh::LeanObject,
        17863078355054839409 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value:
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
    m_data: [105, 115, 84, 114, 117, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value
        ) as *mut leanh::LeanObject,
        16879624741230498429 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value:
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
    m_data: [104, 0],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value
        ) as *mut leanh::LeanObject,
        8738205681931236784 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value:
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
    m_fun: l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value:
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
    m_fun: l_Lean_Meta_MatcherApp_toExpr as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1_value:
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
    m_fun: l_Lean_Expr_isFVar___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 97, 116, 99, 104, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value: leanh::LeanStringObject<
    39,
> = leanh::LeanStringObject {
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
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 112, 114, 111, 111,
        102, 32, 102, 111, 114, 32, 105, 102, 32, 99, 111, 110, 100, 105, 116, 105, 111, 110, 32,
        0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(
    mut v_x_2163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2163_) {
        0 => {
            let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2164_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2164_;
        }
        1 => {
            let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2165_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2165_;
        }
        _ => {
            let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2166_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2166_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___boxed(
    mut v_x_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(v_x_2167_);
    leanh::lean_dec_ref(v_x_2167_);
    return v_res_2168_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(
    mut v_t_2169_: *mut leanh::LeanObject,
    mut v_k_2170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_e_2171_ = leanh::lean_ctor_get(v_t_2169_, 0);
    leanh::lean_inc_ref(v_e_2171_);
    leanh::lean_dec_ref(v_t_2169_);
    v___x_2172_ = leanh::lean_apply_1(v_k_2170_, v_e_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(
    mut v_motive_2173_: *mut leanh::LeanObject,
    mut v_ctorIdx_2174_: *mut leanh::LeanObject,
    mut v_t_2175_: *mut leanh::LeanObject,
    mut v_h_2176_: *mut leanh::LeanObject,
    mut v_k_2177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2175_, v_k_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(
    mut v_motive_2179_: *mut leanh::LeanObject,
    mut v_ctorIdx_2180_: *mut leanh::LeanObject,
    mut v_t_2181_: *mut leanh::LeanObject,
    mut v_h_2182_: *mut leanh::LeanObject,
    mut v_k_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(
        v_motive_2179_,
        v_ctorIdx_2180_,
        v_t_2181_,
        v_h_2182_,
        v_k_2183_,
    );
    leanh::lean_dec(v_ctorIdx_2180_);
    return v_res_2184_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(
    mut v_t_2185_: *mut leanh::LeanObject,
    mut v_ite_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2185_, v_ite_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(
    mut v_motive_2188_: *mut leanh::LeanObject,
    mut v_t_2189_: *mut leanh::LeanObject,
    mut v_h_2190_: *mut leanh::LeanObject,
    mut v_ite_2191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2189_, v_ite_2191_);
    return v___x_2192_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(
    mut v_t_2193_: *mut leanh::LeanObject,
    mut v_dite_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2193_, v_dite_2194_);
    return v___x_2195_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(
    mut v_motive_2196_: *mut leanh::LeanObject,
    mut v_t_2197_: *mut leanh::LeanObject,
    mut v_h_2198_: *mut leanh::LeanObject,
    mut v_dite_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2197_, v_dite_2199_);
    return v___x_2200_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(
    mut v_t_2201_: *mut leanh::LeanObject,
    mut v_matcher_2202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2201_, v_matcher_2202_);
    return v___x_2203_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(
    mut v_motive_2204_: *mut leanh::LeanObject,
    mut v_t_2205_: *mut leanh::LeanObject,
    mut v_h_2206_: *mut leanh::LeanObject,
    mut v_matcher_2207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2208_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2205_, v_matcher_2207_);
    return v___x_2208_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2212_ = leanh::lean_box(0);
    v___x_2213_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1;
    v___x_2214_ = l_Lean_Expr_const___override(v___x_2213_, v___x_2212_);
    return v___x_2214_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2215_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2,
    );
    v___x_2216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2216_, 0, v___x_2215_);
    return v___x_2216_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2217_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3,
    );
    return v___x_2217_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo() -> *mut leanh::LeanObject
{
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2218_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
    return v___x_2218_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(
    mut v_x_2219_: *mut leanh::LeanObject,
    mut v_x_2220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2222_: u8 = 0;
    let mut v_one_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v_body_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2221_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2222_ = lean_nat_dec_eq(v_x_2219_, v_zero_2221_);
                if v_isZero_2222_ == 1 {
                    leanh::lean_dec(v_x_2219_);
                    return v_x_2220_;
                } else {
                    v_one_2223_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2224_ = lean_nat_sub(v_x_2219_, v_one_2223_);
                    leanh::lean_dec(v_x_2219_);
                    if leanh::lean_obj_tag(v_x_2220_) == 1 {
                        v_val_2225_ = leanh::lean_ctor_get(v_x_2220_, 0);
                        v_isSharedCheck_2236_ = (!leanh::lean_is_exclusive(v_x_2220_)) as u8;
                        if v_isSharedCheck_2236_ == 0 {
                            v___x_2227_ = v_x_2220_;
                            v_isShared_2228_ = v_isSharedCheck_2236_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2225_);
                            leanh::lean_dec(v_x_2220_);
                            v___x_2227_ = leanh::lean_box(0);
                            v_isShared_2228_ = v_isSharedCheck_2236_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_x_2220_);
                        v___x_2237_ = leanh::lean_box(0);
                        v_x_2219_ = v_n_2224_;
                        v_x_2220_ = v___x_2237_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_val_2225_) == 6 {
                    v_body_2229_ = leanh::lean_ctor_get(v_val_2225_, 2);
                    leanh::lean_inc_ref(v_body_2229_);
                    leanh::lean_dec_ref_known(v_val_2225_, 3);
                    if v_isShared_2228_ == 0 {
                        leanh::lean_ctor_set(v___x_2227_, 0, v_body_2229_);
                        v___x_2231_ = v___x_2227_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2233_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_body_2229_);
                        v___x_2231_ = v_reuseFailAlloc_2233_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2227_);
                    leanh::lean_dec(v_val_2225_);
                    v___x_2234_ = leanh::lean_box(0);
                    v_x_2219_ = v_n_2224_;
                    v_x_2220_ = v___x_2234_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_x_2219_ = v_n_2224_;
                v_x_2220_ = v___x_2231_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_resTy(
    mut v_info_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherApp_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v_toMatcherInfo_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v_e_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_info_2239_) == 2 {
                    v_matcherApp_2247_ = leanh::lean_ctor_get(v_info_2239_, 0);
                    v_isSharedCheck_2264_ = (!leanh::lean_is_exclusive(v_info_2239_)) as u8;
                    if v_isSharedCheck_2264_ == 0 {
                        v___x_2249_ = v_info_2239_;
                        v_isShared_2250_ = v_isSharedCheck_2264_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_matcherApp_2247_);
                        leanh::lean_dec(v_info_2239_);
                        v___x_2249_ = leanh::lean_box(0);
                        v_isShared_2250_ = v_isSharedCheck_2264_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_e_2265_ = leanh::lean_ctor_get(v_info_2239_, 0);
                    leanh::lean_inc_ref(v_e_2265_);
                    leanh::lean_dec_ref(v_info_2239_);
                    v_e_2241_ = v_e_2265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2242_ = l_Lean_Expr_getAppNumArgs(v_e_2241_);
                v___x_2243_ = leanh::lean_unsigned_to_nat(1);
                v___x_2244_ = lean_nat_sub(v___x_2242_, v___x_2243_);
                leanh::lean_dec(v___x_2242_);
                v___x_2245_ = l_Lean_Expr_getRevArg_x21(v_e_2241_, v___x_2244_);
                leanh::lean_dec_ref(v_e_2241_);
                v___x_2246_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2246_, 0, v___x_2245_);
                return v___x_2246_;
            }
            2 => {
                v_toMatcherInfo_2251_ = leanh::lean_ctor_get(v_matcherApp_2247_, 0);
                leanh::lean_inc_ref(v_toMatcherInfo_2251_);
                v_motive_2252_ = leanh::lean_ctor_get(v_matcherApp_2247_, 4);
                leanh::lean_inc_ref_n(v_motive_2252_, 2);
                leanh::lean_dec_ref(v_matcherApp_2247_);
                v_discrInfos_2253_ = leanh::lean_ctor_get(v_toMatcherInfo_2251_, 4);
                leanh::lean_inc_ref(v_discrInfos_2253_);
                leanh::lean_dec_ref(v_toMatcherInfo_2251_);
                v___x_2254_ = lean_array_get_size(v_discrInfos_2253_);
                leanh::lean_dec_ref(v_discrInfos_2253_);
                if v_isShared_2250_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2249_, 1);
                    leanh::lean_ctor_set(v___x_2249_, 0, v_motive_2252_);
                    v___x_2256_ = v___x_2249_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_motive_2252_);
                    v___x_2256_ = v_reuseFailAlloc_2263_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2257_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(v___x_2254_, v___x_2256_);
                if leanh::lean_obj_tag(v___x_2257_) == 0 {
                    leanh::lean_dec_ref(v_motive_2252_);
                    return v___x_2257_;
                } else {
                    v_val_2258_ = leanh::lean_ctor_get(v___x_2257_, 0);
                    leanh::lean_inc(v_val_2258_);
                    v___x_2259_ = l_Lean_Expr_looseBVarRange(v_val_2258_);
                    leanh::lean_dec(v_val_2258_);
                    v___x_2260_ = l_Lean_Expr_looseBVarRange(v_motive_2252_);
                    leanh::lean_dec_ref(v_motive_2252_);
                    v___x_2261_ = lean_nat_dec_eq(v___x_2259_, v___x_2260_);
                    leanh::lean_dec(v___x_2260_);
                    leanh::lean_dec(v___x_2259_);
                    if v___x_2261_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2257_, 1);
                        v___x_2262_ = leanh::lean_box(0);
                        return v___x_2262_;
                    } else {
                        return v___x_2257_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(
    mut v_matcherApp_2266_: *mut leanh::LeanObject,
    mut v_as_2267_: *mut leanh::LeanObject,
    mut v_i_2268_: *mut leanh::LeanObject,
    mut v_j_2269_: *mut leanh::LeanObject,
    mut v_bs_2270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2272_: u8 = 0;
    let mut v_alts_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2271_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2272_ = lean_nat_dec_eq(v_i_2268_, v_zero_2271_);
                if v_isZero_2272_ == 1 {
                    leanh::lean_dec(v_j_2269_);
                    leanh::lean_dec(v_i_2268_);
                    return v_bs_2270_;
                } else {
                    v_alts_2273_ = leanh::lean_ctor_get(v_matcherApp_2266_, 6);
                    v___x_2274_ = l_Lean_instInhabitedExpr;
                    v_one_2275_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2276_ = lean_nat_sub(v_i_2268_, v_one_2275_);
                    leanh::lean_dec(v_i_2268_);
                    v___x_2277_ = lean_array_fget_borrowed(v_as_2267_, v_j_2269_);
                    v___x_2278_ = lean_array_get_borrowed(v___x_2274_, v_alts_2273_, v_j_2269_);
                    leanh::lean_inc(v___x_2278_);
                    leanh::lean_inc(v___x_2277_);
                    v___x_2279_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
                    leanh::lean_ctor_set(v___x_2279_, 1, v___x_2278_);
                    v___x_2280_ = lean_nat_add(v_j_2269_, v_one_2275_);
                    leanh::lean_dec(v_j_2269_);
                    v___x_2281_ = lean_array_push(v_bs_2270_, v___x_2279_);
                    v_i_2268_ = v_n_2276_;
                    v_j_2269_ = v___x_2280_;
                    v_bs_2270_ = v___x_2281_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(
    mut v_matcherApp_2283_: *mut leanh::LeanObject,
    mut v_as_2284_: *mut leanh::LeanObject,
    mut v_i_2285_: *mut leanh::LeanObject,
    mut v_j_2286_: *mut leanh::LeanObject,
    mut v_bs_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2288_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(
            v_matcherApp_2283_,
            v_as_2284_,
            v_i_2285_,
            v_j_2286_,
            v_bs_2287_,
        );
    leanh::lean_dec_ref(v_as_2284_);
    leanh::lean_dec_ref(v_matcherApp_2283_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(
    mut v_info_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_info_2289_) {
        0 => {
            let mut v_e_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_2290_ = leanh::lean_ctor_get(v_info_2289_, 0);
            leanh::lean_inc_ref(v_e_2290_);
            leanh::lean_dec_ref_known(v_info_2289_, 1);
            v___x_2291_ = leanh::lean_unsigned_to_nat(0);
            v___x_2292_ = leanh::lean_unsigned_to_nat(3);
            v___x_2293_ = l_Lean_Expr_getAppNumArgs(v_e_2290_);
            v___x_2294_ = lean_nat_sub(v___x_2293_, v___x_2292_);
            v___x_2295_ = leanh::lean_unsigned_to_nat(1);
            v___x_2296_ = lean_nat_sub(v___x_2294_, v___x_2295_);
            leanh::lean_dec(v___x_2294_);
            v___x_2297_ = l_Lean_Expr_getRevArg_x21(v_e_2290_, v___x_2296_);
            v___x_2298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2298_, 0, v___x_2291_);
            leanh::lean_ctor_set(v___x_2298_, 1, v___x_2297_);
            v___x_2299_ = leanh::lean_unsigned_to_nat(4);
            v___x_2300_ = lean_nat_sub(v___x_2293_, v___x_2299_);
            leanh::lean_dec(v___x_2293_);
            v___x_2301_ = lean_nat_sub(v___x_2300_, v___x_2295_);
            leanh::lean_dec(v___x_2300_);
            v___x_2302_ = l_Lean_Expr_getRevArg_x21(v_e_2290_, v___x_2301_);
            leanh::lean_dec_ref(v_e_2290_);
            v___x_2303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2303_, 0, v___x_2291_);
            leanh::lean_ctor_set(v___x_2303_, 1, v___x_2302_);
            v___x_2304_ = leanh::lean_unsigned_to_nat(2);
            v___x_2305_ = lean_mk_empty_array_with_capacity(v___x_2304_);
            v___x_2306_ = lean_array_push(v___x_2305_, v___x_2298_);
            v___x_2307_ = lean_array_push(v___x_2306_, v___x_2303_);
            return v___x_2307_;
        }
        1 => {
            let mut v_e_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_e_2308_ = leanh::lean_ctor_get(v_info_2289_, 0);
            leanh::lean_inc_ref(v_e_2308_);
            leanh::lean_dec_ref_known(v_info_2289_, 1);
            v___x_2309_ = leanh::lean_unsigned_to_nat(1);
            v___x_2310_ = leanh::lean_unsigned_to_nat(3);
            v___x_2311_ = l_Lean_Expr_getAppNumArgs(v_e_2308_);
            v___x_2312_ = lean_nat_sub(v___x_2311_, v___x_2310_);
            v___x_2313_ = lean_nat_sub(v___x_2312_, v___x_2309_);
            leanh::lean_dec(v___x_2312_);
            v___x_2314_ = l_Lean_Expr_getRevArg_x21(v_e_2308_, v___x_2313_);
            v___x_2315_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2315_, 0, v___x_2309_);
            leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
            v___x_2316_ = leanh::lean_unsigned_to_nat(4);
            v___x_2317_ = lean_nat_sub(v___x_2311_, v___x_2316_);
            leanh::lean_dec(v___x_2311_);
            v___x_2318_ = lean_nat_sub(v___x_2317_, v___x_2309_);
            leanh::lean_dec(v___x_2317_);
            v___x_2319_ = l_Lean_Expr_getRevArg_x21(v_e_2308_, v___x_2318_);
            leanh::lean_dec_ref(v_e_2308_);
            v___x_2320_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2320_, 0, v___x_2309_);
            leanh::lean_ctor_set(v___x_2320_, 1, v___x_2319_);
            v___x_2321_ = leanh::lean_unsigned_to_nat(2);
            v___x_2322_ = lean_mk_empty_array_with_capacity(v___x_2321_);
            v___x_2323_ = lean_array_push(v___x_2322_, v___x_2315_);
            v___x_2324_ = lean_array_push(v___x_2323_, v___x_2320_);
            return v___x_2324_;
        }
        _ => {
            let mut v_matcherApp_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_matcherApp_2325_ = leanh::lean_ctor_get(v_info_2289_, 0);
            leanh::lean_inc_ref_n(v_matcherApp_2325_, 2);
            leanh::lean_dec_ref_known(v_info_2289_, 1);
            v___x_2326_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2325_);
            v___x_2327_ = lean_array_get_size(v___x_2326_);
            v___x_2328_ = leanh::lean_unsigned_to_nat(0);
            v___x_2329_ = lean_mk_empty_array_with_capacity(v___x_2327_);
            v___x_2330_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_2325_, v___x_2326_, v___x_2327_, v___x_2328_, v___x_2329_);
            leanh::lean_dec_ref(v___x_2326_);
            leanh::lean_dec_ref(v_matcherApp_2325_);
            return v___x_2330_;
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(
    mut v_matcherApp_2331_: *mut leanh::LeanObject,
    mut v_as_2332_: *mut leanh::LeanObject,
    mut v_i_2333_: *mut leanh::LeanObject,
    mut v_j_2334_: *mut leanh::LeanObject,
    mut v_inv_2335_: *mut leanh::LeanObject,
    mut v_bs_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2337_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(
            v_matcherApp_2331_,
            v_as_2332_,
            v_i_2333_,
            v_j_2334_,
            v_bs_2336_,
        );
    return v___x_2337_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(
    mut v_matcherApp_2338_: *mut leanh::LeanObject,
    mut v_as_2339_: *mut leanh::LeanObject,
    mut v_i_2340_: *mut leanh::LeanObject,
    mut v_j_2341_: *mut leanh::LeanObject,
    mut v_inv_2342_: *mut leanh::LeanObject,
    mut v_bs_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2344_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(
        v_matcherApp_2338_,
        v_as_2339_,
        v_i_2340_,
        v_j_2341_,
        v_inv_2342_,
        v_bs_2343_,
    );
    leanh::lean_dec_ref(v_as_2339_);
    leanh::lean_dec_ref(v_matcherApp_2338_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_expr(
    mut v_x_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2345_) == 2 {
        let mut v_matcherApp_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_matcherApp_2346_ = leanh::lean_ctor_get(v_x_2345_, 0);
        leanh::lean_inc_ref(v_matcherApp_2346_);
        leanh::lean_dec_ref_known(v_x_2345_, 1);
        v___x_2347_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_2346_);
        return v___x_2347_;
    } else {
        let mut v_e_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_e_2348_ = leanh::lean_ctor_get(v_x_2345_, 0);
        leanh::lean_inc_ref(v_e_2348_);
        leanh::lean_dec_ref(v_x_2345_);
        return v_e_2348_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(
    mut v___x_2352_: *mut leanh::LeanObject,
    mut v_resTy_2353_: *mut leanh::LeanObject,
    mut v_c_2354_: *mut leanh::LeanObject,
    mut v_dec_2355_: *mut leanh::LeanObject,
    mut v_t_2356_: *mut leanh::LeanObject,
    mut v_e_2357_: *mut leanh::LeanObject,
    mut v_k_2358_: *mut leanh::LeanObject,
    mut v_u_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2360_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1;
    v___x_2361_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2361_, 0, v_u_2359_);
    leanh::lean_ctor_set(v___x_2361_, 1, v___x_2352_);
    v___x_2362_ = l_Lean_mkConst(v___x_2360_, v___x_2361_);
    leanh::lean_inc_ref(v_e_2357_);
    leanh::lean_inc_ref(v_t_2356_);
    leanh::lean_inc_ref(v_dec_2355_);
    leanh::lean_inc_ref(v_c_2354_);
    v___x_2363_ = l_Lean_mkApp5(
        v___x_2362_,
        v_resTy_2353_,
        v_c_2354_,
        v_dec_2355_,
        v_t_2356_,
        v_e_2357_,
    );
    v___x_2364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2364_, 0, v___x_2363_);
    v___x_2365_ = leanh::lean_unsigned_to_nat(4);
    v___x_2366_ = lean_mk_empty_array_with_capacity(v___x_2365_);
    v___x_2367_ = lean_array_push(v___x_2366_, v_c_2354_);
    v___x_2368_ = lean_array_push(v___x_2367_, v_dec_2355_);
    v___x_2369_ = lean_array_push(v___x_2368_, v_t_2356_);
    v___x_2370_ = lean_array_push(v___x_2369_, v_e_2357_);
    v___x_2371_ = leanh::lean_apply_2(v_k_2358_, v___x_2364_, v___x_2370_);
    return v___x_2371_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(
    mut v___x_2372_: *mut leanh::LeanObject,
    mut v_resTy_2373_: *mut leanh::LeanObject,
    mut v_c_2374_: *mut leanh::LeanObject,
    mut v_dec_2375_: *mut leanh::LeanObject,
    mut v_t_2376_: *mut leanh::LeanObject,
    mut v_k_2377_: *mut leanh::LeanObject,
    mut v_inst_2378_: *mut leanh::LeanObject,
    mut v_toBind_2379_: *mut leanh::LeanObject,
    mut v_e_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_resTy_2373_);
    v___f_2381_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2381_, 0, v___x_2372_);
    leanh::lean_closure_set(v___f_2381_, 1, v_resTy_2373_);
    leanh::lean_closure_set(v___f_2381_, 2, v_c_2374_);
    leanh::lean_closure_set(v___f_2381_, 3, v_dec_2375_);
    leanh::lean_closure_set(v___f_2381_, 4, v_t_2376_);
    leanh::lean_closure_set(v___f_2381_, 5, v_e_2380_);
    leanh::lean_closure_set(v___f_2381_, 6, v_k_2377_);
    v___x_2382_ = leanh::lean_alloc_closure(
        l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_2382_, 0, v_resTy_2373_);
    v___x_2383_ = leanh::lean_apply_2(v_inst_2378_, leanh::lean_box(0), v___x_2382_);
    v___x_2384_ = leanh::lean_apply_4(
        v_toBind_2379_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2383_,
        v___f_2381_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(
    mut v___x_2388_: *mut leanh::LeanObject,
    mut v_resTy_2389_: *mut leanh::LeanObject,
    mut v_c_2390_: *mut leanh::LeanObject,
    mut v_dec_2391_: *mut leanh::LeanObject,
    mut v_k_2392_: *mut leanh::LeanObject,
    mut v_inst_2393_: *mut leanh::LeanObject,
    mut v_toBind_2394_: *mut leanh::LeanObject,
    mut v_inst_2395_: *mut leanh::LeanObject,
    mut v_inst_2396_: *mut leanh::LeanObject,
    mut v_t_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_resTy_2389_);
    v___f_2398_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_2398_, 0, v___x_2388_);
    leanh::lean_closure_set(v___f_2398_, 1, v_resTy_2389_);
    leanh::lean_closure_set(v___f_2398_, 2, v_c_2390_);
    leanh::lean_closure_set(v___f_2398_, 3, v_dec_2391_);
    leanh::lean_closure_set(v___f_2398_, 4, v_t_2397_);
    leanh::lean_closure_set(v___f_2398_, 5, v_k_2392_);
    leanh::lean_closure_set(v___f_2398_, 6, v_inst_2393_);
    leanh::lean_closure_set(v___f_2398_, 7, v_toBind_2394_);
    v___x_2399_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1;
    v___x_2400_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2395_,
        v_inst_2396_,
        v___x_2399_,
        v_resTy_2389_,
        v___f_2398_,
    );
    return v___x_2400_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(
    mut v___x_2404_: *mut leanh::LeanObject,
    mut v_resTy_2405_: *mut leanh::LeanObject,
    mut v_c_2406_: *mut leanh::LeanObject,
    mut v_k_2407_: *mut leanh::LeanObject,
    mut v_inst_2408_: *mut leanh::LeanObject,
    mut v_toBind_2409_: *mut leanh::LeanObject,
    mut v_inst_2410_: *mut leanh::LeanObject,
    mut v_inst_2411_: *mut leanh::LeanObject,
    mut v_dec_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2411_);
    leanh::lean_inc_ref(v_inst_2410_);
    leanh::lean_inc_ref(v_resTy_2405_);
    v___f_2413_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_2413_, 0, v___x_2404_);
    leanh::lean_closure_set(v___f_2413_, 1, v_resTy_2405_);
    leanh::lean_closure_set(v___f_2413_, 2, v_c_2406_);
    leanh::lean_closure_set(v___f_2413_, 3, v_dec_2412_);
    leanh::lean_closure_set(v___f_2413_, 4, v_k_2407_);
    leanh::lean_closure_set(v___f_2413_, 5, v_inst_2408_);
    leanh::lean_closure_set(v___f_2413_, 6, v_toBind_2409_);
    leanh::lean_closure_set(v___f_2413_, 7, v_inst_2410_);
    leanh::lean_closure_set(v___f_2413_, 8, v_inst_2411_);
    v___x_2414_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1;
    v___x_2415_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2410_,
        v_inst_2411_,
        v___x_2414_,
        v_resTy_2405_,
        v___f_2413_,
    );
    return v___x_2415_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2422_ = leanh::lean_box(0);
    v___x_2423_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3;
    v___x_2424_ = l_Lean_mkConst(v___x_2423_, v___x_2422_);
    return v___x_2424_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(
    mut v_resTy_2425_: *mut leanh::LeanObject,
    mut v_k_2426_: *mut leanh::LeanObject,
    mut v_inst_2427_: *mut leanh::LeanObject,
    mut v_toBind_2428_: *mut leanh::LeanObject,
    mut v_inst_2429_: *mut leanh::LeanObject,
    mut v_inst_2430_: *mut leanh::LeanObject,
    mut v_c_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1;
    v___x_2433_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_inst_2430_);
    leanh::lean_inc_ref(v_inst_2429_);
    leanh::lean_inc_ref(v_c_2431_);
    v___f_2434_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_2434_, 0, v___x_2433_);
    leanh::lean_closure_set(v___f_2434_, 1, v_resTy_2425_);
    leanh::lean_closure_set(v___f_2434_, 2, v_c_2431_);
    leanh::lean_closure_set(v___f_2434_, 3, v_k_2426_);
    leanh::lean_closure_set(v___f_2434_, 4, v_inst_2427_);
    leanh::lean_closure_set(v___f_2434_, 5, v_toBind_2428_);
    leanh::lean_closure_set(v___f_2434_, 6, v_inst_2429_);
    leanh::lean_closure_set(v___f_2434_, 7, v_inst_2430_);
    v___x_2435_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4,
    );
    v___x_2436_ = l_Lean_Expr_app___override(v___x_2435_, v_c_2431_);
    v___x_2437_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2429_,
        v_inst_2430_,
        v___x_2432_,
        v___x_2436_,
        v___f_2434_,
    );
    return v___x_2437_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(
    mut v_c_2438_: *mut leanh::LeanObject,
    mut v_resTy_2439_: *mut leanh::LeanObject,
    mut v___y_2440_: *mut leanh::LeanObject,
    mut v___y_2441_: *mut leanh::LeanObject,
    mut v___y_2442_: *mut leanh::LeanObject,
    mut v___y_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ = l_Lean_mkArrow(v_c_2438_, v_resTy_2439_, v___y_2442_, v___y_2443_);
    return v___x_2445_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(
    mut v_c_2446_: *mut leanh::LeanObject,
    mut v_resTy_2447_: *mut leanh::LeanObject,
    mut v___y_2448_: *mut leanh::LeanObject,
    mut v___y_2449_: *mut leanh::LeanObject,
    mut v___y_2450_: *mut leanh::LeanObject,
    mut v___y_2451_: *mut leanh::LeanObject,
    mut v___y_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(
        v_c_2446_,
        v_resTy_2447_,
        v___y_2448_,
        v___y_2449_,
        v___y_2450_,
        v___y_2451_,
    );
    leanh::lean_dec(v___y_2451_);
    leanh::lean_dec_ref(v___y_2450_);
    leanh::lean_dec(v___y_2449_);
    leanh::lean_dec_ref(v___y_2448_);
    return v_res_2453_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(
    mut v___x_2457_: *mut leanh::LeanObject,
    mut v_resTy_2458_: *mut leanh::LeanObject,
    mut v_c_2459_: *mut leanh::LeanObject,
    mut v_dec_2460_: *mut leanh::LeanObject,
    mut v_t_2461_: *mut leanh::LeanObject,
    mut v_e_2462_: *mut leanh::LeanObject,
    mut v_k_2463_: *mut leanh::LeanObject,
    mut v_u_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1;
    v___x_2466_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2466_, 0, v_u_2464_);
    leanh::lean_ctor_set(v___x_2466_, 1, v___x_2457_);
    v___x_2467_ = l_Lean_mkConst(v___x_2465_, v___x_2466_);
    leanh::lean_inc_ref(v_e_2462_);
    leanh::lean_inc_ref(v_t_2461_);
    leanh::lean_inc_ref(v_dec_2460_);
    leanh::lean_inc_ref(v_c_2459_);
    v___x_2468_ = l_Lean_mkApp5(
        v___x_2467_,
        v_resTy_2458_,
        v_c_2459_,
        v_dec_2460_,
        v_t_2461_,
        v_e_2462_,
    );
    v___x_2469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2469_, 0, v___x_2468_);
    v___x_2470_ = leanh::lean_unsigned_to_nat(4);
    v___x_2471_ = lean_mk_empty_array_with_capacity(v___x_2470_);
    v___x_2472_ = lean_array_push(v___x_2471_, v_c_2459_);
    v___x_2473_ = lean_array_push(v___x_2472_, v_dec_2460_);
    v___x_2474_ = lean_array_push(v___x_2473_, v_t_2461_);
    v___x_2475_ = lean_array_push(v___x_2474_, v_e_2462_);
    v___x_2476_ = leanh::lean_apply_2(v_k_2463_, v___x_2469_, v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(
    mut v___x_2477_: *mut leanh::LeanObject,
    mut v_resTy_2478_: *mut leanh::LeanObject,
    mut v_c_2479_: *mut leanh::LeanObject,
    mut v_dec_2480_: *mut leanh::LeanObject,
    mut v_t_2481_: *mut leanh::LeanObject,
    mut v_k_2482_: *mut leanh::LeanObject,
    mut v_inst_2483_: *mut leanh::LeanObject,
    mut v_toBind_2484_: *mut leanh::LeanObject,
    mut v_e_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_resTy_2478_);
    v___f_2486_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2486_, 0, v___x_2477_);
    leanh::lean_closure_set(v___f_2486_, 1, v_resTy_2478_);
    leanh::lean_closure_set(v___f_2486_, 2, v_c_2479_);
    leanh::lean_closure_set(v___f_2486_, 3, v_dec_2480_);
    leanh::lean_closure_set(v___f_2486_, 4, v_t_2481_);
    leanh::lean_closure_set(v___f_2486_, 5, v_e_2485_);
    leanh::lean_closure_set(v___f_2486_, 6, v_k_2482_);
    v___x_2487_ = leanh::lean_alloc_closure(
        l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_2487_, 0, v_resTy_2478_);
    v___x_2488_ = leanh::lean_apply_2(v_inst_2483_, leanh::lean_box(0), v___x_2487_);
    v___x_2489_ = leanh::lean_apply_4(
        v_toBind_2484_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2488_,
        v___f_2486_,
    );
    return v___x_2489_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(
    mut v___x_2490_: *mut leanh::LeanObject,
    mut v_resTy_2491_: *mut leanh::LeanObject,
    mut v_c_2492_: *mut leanh::LeanObject,
    mut v_dec_2493_: *mut leanh::LeanObject,
    mut v_k_2494_: *mut leanh::LeanObject,
    mut v_inst_2495_: *mut leanh::LeanObject,
    mut v_toBind_2496_: *mut leanh::LeanObject,
    mut v_inst_2497_: *mut leanh::LeanObject,
    mut v_inst_2498_: *mut leanh::LeanObject,
    mut v_eTy_2499_: *mut leanh::LeanObject,
    mut v_t_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2501_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7 as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_2501_, 0, v___x_2490_);
    leanh::lean_closure_set(v___f_2501_, 1, v_resTy_2491_);
    leanh::lean_closure_set(v___f_2501_, 2, v_c_2492_);
    leanh::lean_closure_set(v___f_2501_, 3, v_dec_2493_);
    leanh::lean_closure_set(v___f_2501_, 4, v_t_2500_);
    leanh::lean_closure_set(v___f_2501_, 5, v_k_2494_);
    leanh::lean_closure_set(v___f_2501_, 6, v_inst_2495_);
    leanh::lean_closure_set(v___f_2501_, 7, v_toBind_2496_);
    v___x_2502_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1;
    v___x_2503_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2497_,
        v_inst_2498_,
        v___x_2502_,
        v_eTy_2499_,
        v___f_2501_,
    );
    return v___x_2503_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(
    mut v___x_2504_: *mut leanh::LeanObject,
    mut v_resTy_2505_: *mut leanh::LeanObject,
    mut v_c_2506_: *mut leanh::LeanObject,
    mut v_dec_2507_: *mut leanh::LeanObject,
    mut v_k_2508_: *mut leanh::LeanObject,
    mut v_inst_2509_: *mut leanh::LeanObject,
    mut v_toBind_2510_: *mut leanh::LeanObject,
    mut v_inst_2511_: *mut leanh::LeanObject,
    mut v_inst_2512_: *mut leanh::LeanObject,
    mut v_tTy_2513_: *mut leanh::LeanObject,
    mut v_eTy_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_2512_);
    leanh::lean_inc_ref(v_inst_2511_);
    v___f_2515_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_2515_, 0, v___x_2504_);
    leanh::lean_closure_set(v___f_2515_, 1, v_resTy_2505_);
    leanh::lean_closure_set(v___f_2515_, 2, v_c_2506_);
    leanh::lean_closure_set(v___f_2515_, 3, v_dec_2507_);
    leanh::lean_closure_set(v___f_2515_, 4, v_k_2508_);
    leanh::lean_closure_set(v___f_2515_, 5, v_inst_2509_);
    leanh::lean_closure_set(v___f_2515_, 6, v_toBind_2510_);
    leanh::lean_closure_set(v___f_2515_, 7, v_inst_2511_);
    leanh::lean_closure_set(v___f_2515_, 8, v_inst_2512_);
    leanh::lean_closure_set(v___f_2515_, 9, v_eTy_2514_);
    v___x_2516_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1;
    v___x_2517_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2511_,
        v_inst_2512_,
        v___x_2516_,
        v_tTy_2513_,
        v___f_2515_,
    );
    return v___x_2517_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(
    mut v___x_2518_: *mut leanh::LeanObject,
    mut v_resTy_2519_: *mut leanh::LeanObject,
    mut v___y_2520_: *mut leanh::LeanObject,
    mut v___y_2521_: *mut leanh::LeanObject,
    mut v___y_2522_: *mut leanh::LeanObject,
    mut v___y_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ = l_Lean_mkArrow(v___x_2518_, v_resTy_2519_, v___y_2522_, v___y_2523_);
    return v___x_2525_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(
    mut v___x_2526_: *mut leanh::LeanObject,
    mut v_resTy_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(
        v___x_2526_,
        v_resTy_2527_,
        v___y_2528_,
        v___y_2529_,
        v___y_2530_,
        v___y_2531_,
    );
    leanh::lean_dec(v___y_2531_);
    leanh::lean_dec_ref(v___y_2530_);
    leanh::lean_dec(v___y_2529_);
    leanh::lean_dec_ref(v___y_2528_);
    return v_res_2533_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(
    mut v___x_2534_: *mut leanh::LeanObject,
    mut v_resTy_2535_: *mut leanh::LeanObject,
    mut v_c_2536_: *mut leanh::LeanObject,
    mut v_dec_2537_: *mut leanh::LeanObject,
    mut v_k_2538_: *mut leanh::LeanObject,
    mut v_inst_2539_: *mut leanh::LeanObject,
    mut v_toBind_2540_: *mut leanh::LeanObject,
    mut v_inst_2541_: *mut leanh::LeanObject,
    mut v_inst_2542_: *mut leanh::LeanObject,
    mut v_tTy_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2540_);
    leanh::lean_inc(v_inst_2539_);
    leanh::lean_inc_ref(v_c_2536_);
    leanh::lean_inc_ref(v_resTy_2535_);
    v___f_2544_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_2544_, 0, v___x_2534_);
    leanh::lean_closure_set(v___f_2544_, 1, v_resTy_2535_);
    leanh::lean_closure_set(v___f_2544_, 2, v_c_2536_);
    leanh::lean_closure_set(v___f_2544_, 3, v_dec_2537_);
    leanh::lean_closure_set(v___f_2544_, 4, v_k_2538_);
    leanh::lean_closure_set(v___f_2544_, 5, v_inst_2539_);
    leanh::lean_closure_set(v___f_2544_, 6, v_toBind_2540_);
    leanh::lean_closure_set(v___f_2544_, 7, v_inst_2541_);
    leanh::lean_closure_set(v___f_2544_, 8, v_inst_2542_);
    leanh::lean_closure_set(v___f_2544_, 9, v_tTy_2543_);
    v___x_2545_ = l_Lean_mkNot(v_c_2536_);
    v___f_2546_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_2546_, 0, v___x_2545_);
    leanh::lean_closure_set(v___f_2546_, 1, v_resTy_2535_);
    v___x_2547_ = leanh::lean_apply_2(v_inst_2539_, leanh::lean_box(0), v___f_2546_);
    v___x_2548_ = leanh::lean_apply_4(
        v_toBind_2540_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2547_,
        v___f_2544_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(
    mut v___x_2549_: *mut leanh::LeanObject,
    mut v_resTy_2550_: *mut leanh::LeanObject,
    mut v_c_2551_: *mut leanh::LeanObject,
    mut v_k_2552_: *mut leanh::LeanObject,
    mut v_inst_2553_: *mut leanh::LeanObject,
    mut v_toBind_2554_: *mut leanh::LeanObject,
    mut v_inst_2555_: *mut leanh::LeanObject,
    mut v_inst_2556_: *mut leanh::LeanObject,
    mut v___f_2557_: *mut leanh::LeanObject,
    mut v_dec_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2554_);
    leanh::lean_inc(v_inst_2553_);
    v___f_2559_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_2559_, 0, v___x_2549_);
    leanh::lean_closure_set(v___f_2559_, 1, v_resTy_2550_);
    leanh::lean_closure_set(v___f_2559_, 2, v_c_2551_);
    leanh::lean_closure_set(v___f_2559_, 3, v_dec_2558_);
    leanh::lean_closure_set(v___f_2559_, 4, v_k_2552_);
    leanh::lean_closure_set(v___f_2559_, 5, v_inst_2553_);
    leanh::lean_closure_set(v___f_2559_, 6, v_toBind_2554_);
    leanh::lean_closure_set(v___f_2559_, 7, v_inst_2555_);
    leanh::lean_closure_set(v___f_2559_, 8, v_inst_2556_);
    v___x_2560_ = leanh::lean_apply_2(v_inst_2553_, leanh::lean_box(0), v___f_2557_);
    v___x_2561_ = leanh::lean_apply_4(
        v_toBind_2554_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2560_,
        v___f_2559_,
    );
    return v___x_2561_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(
    mut v_resTy_2562_: *mut leanh::LeanObject,
    mut v_k_2563_: *mut leanh::LeanObject,
    mut v_inst_2564_: *mut leanh::LeanObject,
    mut v_toBind_2565_: *mut leanh::LeanObject,
    mut v_inst_2566_: *mut leanh::LeanObject,
    mut v_inst_2567_: *mut leanh::LeanObject,
    mut v_c_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_resTy_2562_);
    leanh::lean_inc_ref_n(v_c_2568_, 2);
    v___f_2569_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_2569_, 0, v_c_2568_);
    leanh::lean_closure_set(v___f_2569_, 1, v_resTy_2562_);
    v___x_2570_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1;
    v___x_2571_ = leanh::lean_box(0);
    leanh::lean_inc_ref(v_inst_2567_);
    leanh::lean_inc_ref(v_inst_2566_);
    v___f_2572_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12 as *mut core::ffi::c_void,
        10,
        9,
    );
    leanh::lean_closure_set(v___f_2572_, 0, v___x_2571_);
    leanh::lean_closure_set(v___f_2572_, 1, v_resTy_2562_);
    leanh::lean_closure_set(v___f_2572_, 2, v_c_2568_);
    leanh::lean_closure_set(v___f_2572_, 3, v_k_2563_);
    leanh::lean_closure_set(v___f_2572_, 4, v_inst_2564_);
    leanh::lean_closure_set(v___f_2572_, 5, v_toBind_2565_);
    leanh::lean_closure_set(v___f_2572_, 6, v_inst_2566_);
    leanh::lean_closure_set(v___f_2572_, 7, v_inst_2567_);
    leanh::lean_closure_set(v___f_2572_, 8, v___f_2569_);
    v___x_2573_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4,
    );
    v___x_2574_ = l_Lean_Expr_app___override(v___x_2573_, v_c_2568_);
    v___x_2575_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2566_,
        v_inst_2567_,
        v___x_2570_,
        v___x_2574_,
        v___f_2572_,
    );
    return v___x_2575_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(
    mut v_resTy_2576_: *mut leanh::LeanObject,
    mut v_motiveArgs_2577_: *mut leanh::LeanObject,
    mut v_x_2578_: *mut leanh::LeanObject,
    mut v___y_2579_: *mut leanh::LeanObject,
    mut v___y_2580_: *mut leanh::LeanObject,
    mut v___y_2581_: *mut leanh::LeanObject,
    mut v___y_2582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2584_: u8 = 0;
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = 0;
    v___x_2585_ = 1;
    v___x_2586_ = 1;
    v___x_2587_ = l_Lean_Meta_mkLambdaFVars(
        v_motiveArgs_2577_,
        v_resTy_2576_,
        v___x_2584_,
        v___x_2585_,
        v___x_2584_,
        v___x_2585_,
        v___x_2586_,
        v___y_2579_,
        v___y_2580_,
        v___y_2581_,
        v___y_2582_,
    );
    return v___x_2587_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed(
    mut v_resTy_2588_: *mut leanh::LeanObject,
    mut v_motiveArgs_2589_: *mut leanh::LeanObject,
    mut v_x_2590_: *mut leanh::LeanObject,
    mut v___y_2591_: *mut leanh::LeanObject,
    mut v___y_2592_: *mut leanh::LeanObject,
    mut v___y_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(
        v_resTy_2588_,
        v_motiveArgs_2589_,
        v_x_2590_,
        v___y_2591_,
        v___y_2592_,
        v___y_2593_,
        v___y_2594_,
    );
    leanh::lean_dec(v___y_2594_);
    leanh::lean_dec_ref(v___y_2593_);
    leanh::lean_dec(v___y_2592_);
    leanh::lean_dec_ref(v___y_2591_);
    leanh::lean_dec_ref(v_x_2590_);
    leanh::lean_dec_ref(v_motiveArgs_2589_);
    return v_res_2596_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(
    mut v_i_2600_: *mut leanh::LeanObject,
    mut v_a_2601_: *mut leanh::LeanObject,
    mut v_x_2602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2603_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1;
    v___x_2604_ = leanh::lean_unsigned_to_nat(1);
    v___x_2605_ = lean_nat_add(v_i_2600_, v___x_2604_);
    v___x_2606_ = lean_name_append_index_after(v___x_2603_, v___x_2605_);
    v___x_2607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2607_, 0, v___x_2606_);
    leanh::lean_ctor_set(v___x_2607_, 1, v_a_2601_);
    return v___x_2607_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(
    mut v_i_2608_: *mut leanh::LeanObject,
    mut v_a_2609_: *mut leanh::LeanObject,
    mut v_x_2610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2611_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(
        v_i_2608_, v_a_2609_, v_x_2610_,
    );
    leanh::lean_dec(v_i_2608_);
    return v_res_2611_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(
    mut v_i_2615_: *mut leanh::LeanObject,
    mut v_toPure_2616_: *mut leanh::LeanObject,
    mut v_____do__lift_2617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2618_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1;
    v___x_2619_ = leanh::lean_unsigned_to_nat(1);
    v___x_2620_ = lean_nat_add(v_i_2615_, v___x_2619_);
    v___x_2621_ = lean_name_append_index_after(v___x_2618_, v___x_2620_);
    v___x_2622_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2622_, 0, v___x_2621_);
    leanh::lean_ctor_set(v___x_2622_, 1, v_____do__lift_2617_);
    v___x_2623_ =
        leanh::lean_apply_2(v_toPure_2616_, leanh::lean_box(0), v___x_2622_);
    return v___x_2623_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(
    mut v_i_2624_: *mut leanh::LeanObject,
    mut v_toPure_2625_: *mut leanh::LeanObject,
    mut v_____do__lift_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(
        v_i_2624_,
        v_toPure_2625_,
        v_____do__lift_2626_,
    );
    leanh::lean_dec(v_i_2624_);
    return v_res_2627_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(
    mut v_toPure_2628_: *mut leanh::LeanObject,
    mut v_inst_2629_: *mut leanh::LeanObject,
    mut v_toBind_2630_: *mut leanh::LeanObject,
    mut v_i_2631_: *mut leanh::LeanObject,
    mut v_a_2632_: *mut leanh::LeanObject,
    mut v_x_2633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2634_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2634_, 0, v_i_2631_);
    leanh::lean_closure_set(v___f_2634_, 1, v_toPure_2628_);
    v___x_2635_ = leanh::lean_alloc_closure(
        l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___x_2635_, 0, v_a_2632_);
    v___x_2636_ = leanh::lean_apply_2(v_inst_2629_, leanh::lean_box(0), v___x_2635_);
    v___x_2637_ = leanh::lean_apply_4(
        v_toBind_2630_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2636_,
        v___f_2634_,
    );
    return v___x_2637_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(
    mut v_toMatcherInfo_2640_: *mut leanh::LeanObject,
    mut v_matcherName_2641_: *mut leanh::LeanObject,
    mut v_matcherLevels_2642_: *mut leanh::LeanObject,
    mut v_params_2643_: *mut leanh::LeanObject,
    mut v_motive_2644_: *mut leanh::LeanObject,
    mut v_discrs_2645_: *mut leanh::LeanObject,
    mut v_alts_2646_: *mut leanh::LeanObject,
    mut v_k_2647_: *mut leanh::LeanObject,
    mut v_____do__lift_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abstractMatcherApp_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2649_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    leanh::lean_inc_ref(v_discrs_2645_);
    v_abstractMatcherApp_2650_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 0, v_toMatcherInfo_2640_);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 1, v_matcherName_2641_);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 2, v_matcherLevels_2642_);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 3, v_params_2643_);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 4, v_motive_2644_);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 5, v_discrs_2645_);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 6, v_____do__lift_2648_);
    leanh::lean_ctor_set(v_abstractMatcherApp_2650_, 7, v___x_2649_);
    v___x_2651_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2651_, 0, v_abstractMatcherApp_2650_);
    v___x_2652_ = l_Array_append___redArg(v_discrs_2645_, v_alts_2646_);
    v___x_2653_ = leanh::lean_apply_2(v_k_2647_, v___x_2651_, v___x_2652_);
    return v___x_2653_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(
    mut v_toMatcherInfo_2654_: *mut leanh::LeanObject,
    mut v_matcherName_2655_: *mut leanh::LeanObject,
    mut v_matcherLevels_2656_: *mut leanh::LeanObject,
    mut v_params_2657_: *mut leanh::LeanObject,
    mut v_motive_2658_: *mut leanh::LeanObject,
    mut v_discrs_2659_: *mut leanh::LeanObject,
    mut v_alts_2660_: *mut leanh::LeanObject,
    mut v_k_2661_: *mut leanh::LeanObject,
    mut v_____do__lift_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2663_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(
        v_toMatcherInfo_2654_,
        v_matcherName_2655_,
        v_matcherLevels_2656_,
        v_params_2657_,
        v_motive_2658_,
        v_discrs_2659_,
        v_alts_2660_,
        v_k_2661_,
        v_____do__lift_2662_,
    );
    leanh::lean_dec_ref(v_alts_2660_);
    return v_res_2663_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(
    mut v_toMatcherInfo_2665_: *mut leanh::LeanObject,
    mut v_matcherName_2666_: *mut leanh::LeanObject,
    mut v_matcherLevels_2667_: *mut leanh::LeanObject,
    mut v_params_2668_: *mut leanh::LeanObject,
    mut v_motive_2669_: *mut leanh::LeanObject,
    mut v_discrs_2670_: *mut leanh::LeanObject,
    mut v_k_2671_: *mut leanh::LeanObject,
    mut v___x_2672_: *mut leanh::LeanObject,
    mut v_inst_2673_: *mut leanh::LeanObject,
    mut v_toBind_2674_: *mut leanh::LeanObject,
    mut v_alts_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2678_: usize = 0;
    let mut v___x_2679_: usize = 0;
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_alts_2675_);
    v___f_2676_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    leanh::lean_closure_set(v___f_2676_, 0, v_toMatcherInfo_2665_);
    leanh::lean_closure_set(v___f_2676_, 1, v_matcherName_2666_);
    leanh::lean_closure_set(v___f_2676_, 2, v_matcherLevels_2667_);
    leanh::lean_closure_set(v___f_2676_, 3, v_params_2668_);
    leanh::lean_closure_set(v___f_2676_, 4, v_motive_2669_);
    leanh::lean_closure_set(v___f_2676_, 5, v_discrs_2670_);
    leanh::lean_closure_set(v___f_2676_, 6, v_alts_2675_);
    leanh::lean_closure_set(v___f_2676_, 7, v_k_2671_);
    v___x_2677_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0;
    v_sz_2678_ = lean_array_size(v_alts_2675_);
    v___x_2679_ = 0usize;
    v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2672_,
        v___x_2677_,
        v_sz_2678_,
        v___x_2679_,
        v_alts_2675_,
    );
    v___x_2681_ = leanh::lean_apply_2(v_inst_2673_, leanh::lean_box(0), v___x_2680_);
    v___x_2682_ = leanh::lean_apply_4(
        v_toBind_2674_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2681_,
        v___f_2676_,
    );
    return v___x_2682_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(
    mut v___f_2702_: *mut leanh::LeanObject,
    mut v_inst_2703_: *mut leanh::LeanObject,
    mut v_inst_2704_: *mut leanh::LeanObject,
    mut v___f_2705_: *mut leanh::LeanObject,
    mut v_origAltTypes_2706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_altNamesTypes_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2707_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9;
    v___x_2708_ = lean_array_get_size(v_origAltTypes_2706_);
    v___x_2709_ = leanh::lean_unsigned_to_nat(0);
    v___x_2710_ = lean_mk_empty_array_with_capacity(v___x_2708_);
    v_altNamesTypes_2711_ = l_Array_mapFinIdxM_map___redArg(
        v___x_2707_,
        v_origAltTypes_2706_,
        v___f_2702_,
        v___x_2708_,
        v___x_2709_,
        v___x_2710_,
    );
    v___x_2712_ = 0;
    v___x_2713_ = l_Lean_Meta_withLocalDeclsDND___redArg(
        v_inst_2703_,
        v_inst_2704_,
        v_altNamesTypes_2711_,
        v___f_2705_,
        v___x_2712_,
    );
    return v___x_2713_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(
    mut v_toMatcherInfo_2714_: *mut leanh::LeanObject,
    mut v_matcherName_2715_: *mut leanh::LeanObject,
    mut v_params_2716_: *mut leanh::LeanObject,
    mut v_motive_2717_: *mut leanh::LeanObject,
    mut v_discrs_2718_: *mut leanh::LeanObject,
    mut v_k_2719_: *mut leanh::LeanObject,
    mut v___x_2720_: *mut leanh::LeanObject,
    mut v_inst_2721_: *mut leanh::LeanObject,
    mut v_toBind_2722_: *mut leanh::LeanObject,
    mut v___f_2723_: *mut leanh::LeanObject,
    mut v_inst_2724_: *mut leanh::LeanObject,
    mut v_inst_2725_: *mut leanh::LeanObject,
    mut v_alts_2726_: *mut leanh::LeanObject,
    mut v_matcherLevels_2727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherPartial_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherPartial_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherPartial_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2722_);
    leanh::lean_inc(v_inst_2721_);
    leanh::lean_inc_ref(v_discrs_2718_);
    leanh::lean_inc_ref(v_motive_2717_);
    leanh::lean_inc_ref(v_params_2716_);
    leanh::lean_inc_ref(v_matcherLevels_2727_);
    leanh::lean_inc(v_matcherName_2715_);
    v___f_2728_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_2728_, 0, v_toMatcherInfo_2714_);
    leanh::lean_closure_set(v___f_2728_, 1, v_matcherName_2715_);
    leanh::lean_closure_set(v___f_2728_, 2, v_matcherLevels_2727_);
    leanh::lean_closure_set(v___f_2728_, 3, v_params_2716_);
    leanh::lean_closure_set(v___f_2728_, 4, v_motive_2717_);
    leanh::lean_closure_set(v___f_2728_, 5, v_discrs_2718_);
    leanh::lean_closure_set(v___f_2728_, 6, v_k_2719_);
    leanh::lean_closure_set(v___f_2728_, 7, v___x_2720_);
    leanh::lean_closure_set(v___f_2728_, 8, v_inst_2721_);
    leanh::lean_closure_set(v___f_2728_, 9, v_toBind_2722_);
    v___f_2729_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2729_, 0, v___f_2723_);
    leanh::lean_closure_set(v___f_2729_, 1, v_inst_2724_);
    leanh::lean_closure_set(v___f_2729_, 2, v_inst_2725_);
    leanh::lean_closure_set(v___f_2729_, 3, v___f_2728_);
    v___x_2730_ = lean_array_to_list(v_matcherLevels_2727_);
    v___x_2731_ = l_Lean_mkConst(v_matcherName_2715_, v___x_2730_);
    v_matcherPartial_2732_ = l_Lean_mkAppN(v___x_2731_, v_params_2716_);
    leanh::lean_dec_ref(v_params_2716_);
    v_matcherPartial_2733_ = l_Lean_Expr_app___override(v_matcherPartial_2732_, v_motive_2717_);
    v_matcherPartial_2734_ = l_Lean_mkAppN(v_matcherPartial_2733_, v_discrs_2718_);
    leanh::lean_dec_ref(v_discrs_2718_);
    v___x_2735_ = lean_array_get_size(v_alts_2726_);
    v___x_2736_ = leanh::lean_alloc_closure(
        l_Lean_Meta_inferArgumentTypesN___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___x_2736_, 0, v___x_2735_);
    leanh::lean_closure_set(v___x_2736_, 1, v_matcherPartial_2734_);
    v___x_2737_ = leanh::lean_apply_2(v_inst_2721_, leanh::lean_box(0), v___x_2736_);
    v___x_2738_ = leanh::lean_apply_4(
        v_toBind_2722_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2737_,
        v___f_2729_,
    );
    return v___x_2738_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(
    mut v_toMatcherInfo_2739_: *mut leanh::LeanObject,
    mut v_matcherName_2740_: *mut leanh::LeanObject,
    mut v_params_2741_: *mut leanh::LeanObject,
    mut v_motive_2742_: *mut leanh::LeanObject,
    mut v_discrs_2743_: *mut leanh::LeanObject,
    mut v_k_2744_: *mut leanh::LeanObject,
    mut v___x_2745_: *mut leanh::LeanObject,
    mut v_inst_2746_: *mut leanh::LeanObject,
    mut v_toBind_2747_: *mut leanh::LeanObject,
    mut v___f_2748_: *mut leanh::LeanObject,
    mut v_inst_2749_: *mut leanh::LeanObject,
    mut v_inst_2750_: *mut leanh::LeanObject,
    mut v_alts_2751_: *mut leanh::LeanObject,
    mut v_matcherLevels_2752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2753_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(
        v_toMatcherInfo_2739_,
        v_matcherName_2740_,
        v_params_2741_,
        v_motive_2742_,
        v_discrs_2743_,
        v_k_2744_,
        v___x_2745_,
        v_inst_2746_,
        v_toBind_2747_,
        v___f_2748_,
        v_inst_2749_,
        v_inst_2750_,
        v_alts_2751_,
        v_matcherLevels_2752_,
    );
    leanh::lean_dec_ref(v_alts_2751_);
    return v_res_2753_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(
    mut v___f_2754_: *mut leanh::LeanObject,
    mut v_matcherLevels_2755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2756_ = leanh::lean_apply_1(v___f_2754_, v_matcherLevels_2755_);
    return v___x_2756_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(
    mut v_matcherLevels_2757_: *mut leanh::LeanObject,
    mut v_val_2758_: *mut leanh::LeanObject,
    mut v_toPure_2759_: *mut leanh::LeanObject,
    mut v_toBind_2760_: *mut leanh::LeanObject,
    mut v___f_2761_: *mut leanh::LeanObject,
    mut v_uElim_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2763_ = lean_array_set(v_matcherLevels_2757_, v_val_2758_, v_uElim_2762_);
    v___x_2764_ =
        leanh::lean_apply_2(v_toPure_2759_, leanh::lean_box(0), v___x_2763_);
    v___x_2765_ = leanh::lean_apply_4(
        v_toBind_2760_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2764_,
        v___f_2761_,
    );
    return v___x_2765_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(
    mut v_matcherLevels_2766_: *mut leanh::LeanObject,
    mut v_val_2767_: *mut leanh::LeanObject,
    mut v_toPure_2768_: *mut leanh::LeanObject,
    mut v_toBind_2769_: *mut leanh::LeanObject,
    mut v___f_2770_: *mut leanh::LeanObject,
    mut v_uElim_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(
        v_matcherLevels_2766_,
        v_val_2767_,
        v_toPure_2768_,
        v_toBind_2769_,
        v___f_2770_,
        v_uElim_2771_,
    );
    leanh::lean_dec(v_val_2767_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(
    mut v_toMatcherInfo_2773_: *mut leanh::LeanObject,
    mut v_matcherName_2774_: *mut leanh::LeanObject,
    mut v_params_2775_: *mut leanh::LeanObject,
    mut v_discrs_2776_: *mut leanh::LeanObject,
    mut v_k_2777_: *mut leanh::LeanObject,
    mut v___x_2778_: *mut leanh::LeanObject,
    mut v_inst_2779_: *mut leanh::LeanObject,
    mut v_toBind_2780_: *mut leanh::LeanObject,
    mut v___f_2781_: *mut leanh::LeanObject,
    mut v_inst_2782_: *mut leanh::LeanObject,
    mut v_inst_2783_: *mut leanh::LeanObject,
    mut v_alts_2784_: *mut leanh::LeanObject,
    mut v_toPure_2785_: *mut leanh::LeanObject,
    mut v_matcherLevels_2786_: *mut leanh::LeanObject,
    mut v_resTy_2787_: *mut leanh::LeanObject,
    mut v_motive_2788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_uElimPos_x3f_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_uElimPos_x3f_2789_ = leanh::lean_ctor_get(v_toMatcherInfo_2773_, 3);
    leanh::lean_inc(v_uElimPos_x3f_2789_);
    leanh::lean_inc(v_toBind_2780_);
    leanh::lean_inc(v_inst_2779_);
    v___f_2790_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed
            as *mut core::ffi::c_void,
        14,
        13,
    );
    leanh::lean_closure_set(v___f_2790_, 0, v_toMatcherInfo_2773_);
    leanh::lean_closure_set(v___f_2790_, 1, v_matcherName_2774_);
    leanh::lean_closure_set(v___f_2790_, 2, v_params_2775_);
    leanh::lean_closure_set(v___f_2790_, 3, v_motive_2788_);
    leanh::lean_closure_set(v___f_2790_, 4, v_discrs_2776_);
    leanh::lean_closure_set(v___f_2790_, 5, v_k_2777_);
    leanh::lean_closure_set(v___f_2790_, 6, v___x_2778_);
    leanh::lean_closure_set(v___f_2790_, 7, v_inst_2779_);
    leanh::lean_closure_set(v___f_2790_, 8, v_toBind_2780_);
    leanh::lean_closure_set(v___f_2790_, 9, v___f_2781_);
    leanh::lean_closure_set(v___f_2790_, 10, v_inst_2782_);
    leanh::lean_closure_set(v___f_2790_, 11, v_inst_2783_);
    leanh::lean_closure_set(v___f_2790_, 12, v_alts_2784_);
    if leanh::lean_obj_tag(v_uElimPos_x3f_2789_) == 0 {
        let mut v___f_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_resTy_2787_);
        leanh::lean_dec(v_inst_2779_);
        v___f_2791_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22
                as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_2791_, 0, v___f_2790_);
        v___x_2792_ = leanh::lean_apply_2(
            v_toPure_2785_,
            leanh::lean_box(0),
            v_matcherLevels_2786_,
        );
        v___x_2793_ = leanh::lean_apply_4(
            v_toBind_2780_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2792_,
            v___f_2791_,
        );
        return v___x_2793_;
    } else {
        let mut v_val_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2794_ = leanh::lean_ctor_get(v_uElimPos_x3f_2789_, 0);
        leanh::lean_inc(v_val_2794_);
        leanh::lean_dec_ref_known(v_uElimPos_x3f_2789_, 1);
        v___f_2795_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22
                as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_2795_, 0, v___f_2790_);
        leanh::lean_inc(v_toBind_2780_);
        v___f_2796_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        leanh::lean_closure_set(v___f_2796_, 0, v_matcherLevels_2786_);
        leanh::lean_closure_set(v___f_2796_, 1, v_val_2794_);
        leanh::lean_closure_set(v___f_2796_, 2, v_toPure_2785_);
        leanh::lean_closure_set(v___f_2796_, 3, v_toBind_2780_);
        leanh::lean_closure_set(v___f_2796_, 4, v___f_2795_);
        v___x_2797_ = leanh::lean_alloc_closure(
            l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void,
            6,
            1,
        );
        leanh::lean_closure_set(v___x_2797_, 0, v_resTy_2787_);
        v___x_2798_ =
            leanh::lean_apply_2(v_inst_2779_, leanh::lean_box(0), v___x_2797_);
        v___x_2799_ = leanh::lean_apply_4(
            v_toBind_2780_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2798_,
            v___f_2796_,
        );
        return v___x_2799_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(
    mut v_toMatcherInfo_2800_: *mut leanh::LeanObject,
    mut v_matcherName_2801_: *mut leanh::LeanObject,
    mut v_params_2802_: *mut leanh::LeanObject,
    mut v_k_2803_: *mut leanh::LeanObject,
    mut v___x_2804_: *mut leanh::LeanObject,
    mut v_inst_2805_: *mut leanh::LeanObject,
    mut v_toBind_2806_: *mut leanh::LeanObject,
    mut v___f_2807_: *mut leanh::LeanObject,
    mut v_inst_2808_: *mut leanh::LeanObject,
    mut v_inst_2809_: *mut leanh::LeanObject,
    mut v_alts_2810_: *mut leanh::LeanObject,
    mut v_toPure_2811_: *mut leanh::LeanObject,
    mut v_matcherLevels_2812_: *mut leanh::LeanObject,
    mut v_resTy_2813_: *mut leanh::LeanObject,
    mut v___x_2814_: *mut leanh::LeanObject,
    mut v_motive_2815_: *mut leanh::LeanObject,
    mut v___f_2816_: *mut leanh::LeanObject,
    mut v_discrs_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_toBind_2806_);
    leanh::lean_inc(v_inst_2805_);
    leanh::lean_inc_ref(v___x_2804_);
    v___f_2818_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23 as *mut core::ffi::c_void,
        16,
        15,
    );
    leanh::lean_closure_set(v___f_2818_, 0, v_toMatcherInfo_2800_);
    leanh::lean_closure_set(v___f_2818_, 1, v_matcherName_2801_);
    leanh::lean_closure_set(v___f_2818_, 2, v_params_2802_);
    leanh::lean_closure_set(v___f_2818_, 3, v_discrs_2817_);
    leanh::lean_closure_set(v___f_2818_, 4, v_k_2803_);
    leanh::lean_closure_set(v___f_2818_, 5, v___x_2804_);
    leanh::lean_closure_set(v___f_2818_, 6, v_inst_2805_);
    leanh::lean_closure_set(v___f_2818_, 7, v_toBind_2806_);
    leanh::lean_closure_set(v___f_2818_, 8, v___f_2807_);
    leanh::lean_closure_set(v___f_2818_, 9, v_inst_2808_);
    leanh::lean_closure_set(v___f_2818_, 10, v_inst_2809_);
    leanh::lean_closure_set(v___f_2818_, 11, v_alts_2810_);
    leanh::lean_closure_set(v___f_2818_, 12, v_toPure_2811_);
    leanh::lean_closure_set(v___f_2818_, 13, v_matcherLevels_2812_);
    leanh::lean_closure_set(v___f_2818_, 14, v_resTy_2813_);
    v___x_2819_ = 0;
    v___x_2820_ = l_Lean_Meta_lambdaTelescope___redArg(
        v___x_2814_,
        v___x_2804_,
        v_motive_2815_,
        v___f_2816_,
        v___x_2819_,
    );
    v___x_2821_ = leanh::lean_apply_2(v_inst_2805_, leanh::lean_box(0), v___x_2820_);
    v___x_2822_ = leanh::lean_apply_4(
        v_toBind_2806_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2821_,
        v___f_2818_,
    );
    return v___x_2822_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMatcherInfo_2823_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_matcherName_2824_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_params_2825_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_k_2826_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_2827_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_inst_2828_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_toBind_2829_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___f_2830_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_2831_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_inst_2832_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_alts_2833_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_toPure_2834_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_matcherLevels_2835_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_resTy_2836_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___x_2837_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_motive_2838_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___f_2839_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_discrs_2840_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2841_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(
        v_toMatcherInfo_2823_,
        v_matcherName_2824_,
        v_params_2825_,
        v_k_2826_,
        v___x_2827_,
        v_inst_2828_,
        v_toBind_2829_,
        v___f_2830_,
        v_inst_2831_,
        v_inst_2832_,
        v_alts_2833_,
        v_toPure_2834_,
        v_matcherLevels_2835_,
        v_resTy_2836_,
        v___x_2837_,
        v_motive_2838_,
        v___f_2839_,
        v_discrs_2840_,
    );
    return v_res_2841_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(
    mut v_inst_2842_: *mut leanh::LeanObject,
    mut v_inst_2843_: *mut leanh::LeanObject,
    mut v___f_2844_: *mut leanh::LeanObject,
    mut v_discrNamesTypes_2845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2846_ = 0;
    v___x_2847_ = l_Lean_Meta_withLocalDeclsDND___redArg(
        v_inst_2842_,
        v_inst_2843_,
        v_discrNamesTypes_2845_,
        v___f_2844_,
        v___x_2846_,
    );
    return v___x_2847_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2848_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2848_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2849_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0,
    );
    v___x_2850_ = l_StateRefT_x27_instMonad___redArg(v___x_2849_);
    return v___x_2850_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2858_ = leanh::lean_unsigned_to_nat(0);
    v___x_2859_ = l_Lean_Level_ofNat(v___x_2858_);
    return v___x_2859_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2860_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once
        ),
        _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8,
    );
    v___x_2861_ = l_Lean_mkSort(v___x_2860_);
    return v___x_2861_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(
    mut v_inst_2863_: *mut leanh::LeanObject,
    mut v_inst_2864_: *mut leanh::LeanObject,
    mut v_inst_2865_: *mut leanh::LeanObject,
    mut v_info_2866_: *mut leanh::LeanObject,
    mut v_resTy_2867_: *mut leanh::LeanObject,
    mut v_k_2868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v_toFunctor_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___f_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherApp_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMatcherInfo_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherName_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherLevels_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v_unused_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_unused_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2869_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1,
                );
                v_toApplicative_2870_ = leanh::lean_ctor_get(v___x_2869_, 0);
                v_toFunctor_2871_ = leanh::lean_ctor_get(v_toApplicative_2870_, 0);
                v_toSeq_2872_ = leanh::lean_ctor_get(v_toApplicative_2870_, 2);
                v_toSeqLeft_2873_ = leanh::lean_ctor_get(v_toApplicative_2870_, 3);
                v_toSeqRight_2874_ = leanh::lean_ctor_get(v_toApplicative_2870_, 4);
                v___f_2875_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2;
                v___f_2876_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_2871_, 2);
                v___f_2877_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2877_, 0, v_toFunctor_2871_);
                v___f_2878_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2878_, 0, v_toFunctor_2871_);
                v___x_2879_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2879_, 0, v___f_2877_);
                leanh::lean_ctor_set(v___x_2879_, 1, v___f_2878_);
                leanh::lean_inc(v_toSeqRight_2874_);
                v___f_2880_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2880_, 0, v_toSeqRight_2874_);
                leanh::lean_inc(v_toSeqLeft_2873_);
                v___f_2881_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2881_, 0, v_toSeqLeft_2873_);
                leanh::lean_inc(v_toSeq_2872_);
                v___f_2882_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2882_, 0, v_toSeq_2872_);
                v___x_2883_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2883_, 0, v___x_2879_);
                leanh::lean_ctor_set(v___x_2883_, 1, v___f_2875_);
                leanh::lean_ctor_set(v___x_2883_, 2, v___f_2882_);
                leanh::lean_ctor_set(v___x_2883_, 3, v___f_2881_);
                leanh::lean_ctor_set(v___x_2883_, 4, v___f_2880_);
                v___x_2884_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2884_, 0, v___x_2883_);
                leanh::lean_ctor_set(v___x_2884_, 1, v___f_2876_);
                v___x_2885_ = l_StateRefT_x27_instMonad___redArg(v___x_2884_);
                v___x_2886_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_2886_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2886_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_2886_, 2, v___x_2885_);
                v___x_2887_ = l_instMonadControlTOfPure___redArg(v___x_2886_);
                v_toApplicative_2888_ = leanh::lean_ctor_get(v___x_2869_, 0);
                v_toFunctor_2889_ = leanh::lean_ctor_get(v_toApplicative_2888_, 0);
                v_toSeq_2890_ = leanh::lean_ctor_get(v_toApplicative_2888_, 2);
                v_toSeqLeft_2891_ = leanh::lean_ctor_get(v_toApplicative_2888_, 3);
                v_toSeqRight_2892_ = leanh::lean_ctor_get(v_toApplicative_2888_, 4);
                leanh::lean_inc_ref_n(v_toFunctor_2889_, 2);
                v___f_2893_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2893_, 0, v_toFunctor_2889_);
                v___f_2894_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2894_, 0, v_toFunctor_2889_);
                v___x_2895_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2895_, 0, v___f_2893_);
                leanh::lean_ctor_set(v___x_2895_, 1, v___f_2894_);
                leanh::lean_inc(v_toSeqRight_2892_);
                v___f_2896_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2896_, 0, v_toSeqRight_2892_);
                leanh::lean_inc(v_toSeqLeft_2891_);
                v___f_2897_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2897_, 0, v_toSeqLeft_2891_);
                leanh::lean_inc(v_toSeq_2890_);
                v___f_2898_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2898_, 0, v_toSeq_2890_);
                v___x_2899_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2899_, 0, v___x_2895_);
                leanh::lean_ctor_set(v___x_2899_, 1, v___f_2875_);
                leanh::lean_ctor_set(v___x_2899_, 2, v___f_2898_);
                leanh::lean_ctor_set(v___x_2899_, 3, v___f_2897_);
                leanh::lean_ctor_set(v___x_2899_, 4, v___f_2896_);
                v___x_2900_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2900_, 0, v___x_2899_);
                leanh::lean_ctor_set(v___x_2900_, 1, v___f_2876_);
                v___x_2901_ = l_StateRefT_x27_instMonad___redArg(v___x_2900_);
                v_toApplicative_2902_ = leanh::lean_ctor_get(v___x_2901_, 0);
                v_isSharedCheck_2960_ = (!leanh::lean_is_exclusive(v___x_2901_)) as u8;
                if v_isSharedCheck_2960_ == 0 {
                    v_unused_2961_ = leanh::lean_ctor_get(v___x_2901_, 1);
                    leanh::lean_dec(v_unused_2961_);
                    v___x_2904_ = v___x_2901_;
                    v_isShared_2905_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2902_);
                    leanh::lean_dec(v___x_2901_);
                    v___x_2904_ = leanh::lean_box(0);
                    v_isShared_2905_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2906_ = leanh::lean_ctor_get(v_toApplicative_2902_, 0);
                v_toSeq_2907_ = leanh::lean_ctor_get(v_toApplicative_2902_, 2);
                v_toSeqLeft_2908_ = leanh::lean_ctor_get(v_toApplicative_2902_, 3);
                v_toSeqRight_2909_ = leanh::lean_ctor_get(v_toApplicative_2902_, 4);
                v_isSharedCheck_2958_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2902_)) as u8;
                if v_isSharedCheck_2958_ == 0 {
                    v_unused_2959_ = leanh::lean_ctor_get(v_toApplicative_2902_, 1);
                    leanh::lean_dec(v_unused_2959_);
                    v___x_2911_ = v_toApplicative_2902_;
                    v_isShared_2912_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2909_);
                    leanh::lean_inc(v_toSeqLeft_2908_);
                    leanh::lean_inc(v_toSeq_2907_);
                    leanh::lean_inc(v_toFunctor_2906_);
                    leanh::lean_dec(v_toApplicative_2902_);
                    v___x_2911_ = leanh::lean_box(0);
                    v_isShared_2912_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2913_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4;
                v___f_2914_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_2906_);
                v___f_2915_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2915_, 0, v_toFunctor_2906_);
                v___f_2916_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2916_, 0, v_toFunctor_2906_);
                v___x_2917_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2917_, 0, v___f_2915_);
                leanh::lean_ctor_set(v___x_2917_, 1, v___f_2916_);
                v___f_2918_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2918_, 0, v_toSeqRight_2909_);
                v___f_2919_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2919_, 0, v_toSeqLeft_2908_);
                v___f_2920_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2920_, 0, v_toSeq_2907_);
                if v_isShared_2912_ == 0 {
                    leanh::lean_ctor_set(v___x_2911_, 4, v___f_2918_);
                    leanh::lean_ctor_set(v___x_2911_, 3, v___f_2919_);
                    leanh::lean_ctor_set(v___x_2911_, 2, v___f_2920_);
                    leanh::lean_ctor_set(v___x_2911_, 1, v___f_2913_);
                    leanh::lean_ctor_set(v___x_2911_, 0, v___x_2917_);
                    v___x_2922_ = v___x_2911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2957_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2917_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___f_2913_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 2, v___f_2920_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 3, v___f_2919_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 4, v___f_2918_);
                    v___x_2922_ = v_reuseFailAlloc_2957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2905_ == 0 {
                    leanh::lean_ctor_set(v___x_2904_, 1, v___f_2914_);
                    leanh::lean_ctor_set(v___x_2904_, 0, v___x_2922_);
                    v___x_2924_ = v___x_2904_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___f_2914_);
                    v___x_2924_ = v_reuseFailAlloc_2956_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                match leanh::lean_obj_tag(v_info_2866_) {
                    0 => {
                        leanh::lean_dec_ref_known(v_info_2866_, 1);
                        leanh::lean_dec_ref(v___x_2924_);
                        leanh::lean_dec_ref(v___x_2887_);
                        v_toBind_2925_ = leanh::lean_ctor_get(v_inst_2865_, 1);
                        leanh::lean_inc_ref(v_inst_2865_);
                        leanh::lean_inc_ref(v_inst_2864_);
                        leanh::lean_inc(v_toBind_2925_);
                        v___f_2926_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4
                                as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        leanh::lean_closure_set(v___f_2926_, 0, v_resTy_2867_);
                        leanh::lean_closure_set(v___f_2926_, 1, v_k_2868_);
                        leanh::lean_closure_set(v___f_2926_, 2, v_inst_2863_);
                        leanh::lean_closure_set(v___f_2926_, 3, v_toBind_2925_);
                        leanh::lean_closure_set(v___f_2926_, 4, v_inst_2864_);
                        leanh::lean_closure_set(v___f_2926_, 5, v_inst_2865_);
                        v___x_2927_ =
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7;
                        v___x_2928_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once), _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
                        v___x_2929_ = l_Lean_Meta_withLocalDeclD___redArg(
                            v_inst_2864_,
                            v_inst_2865_,
                            v___x_2927_,
                            v___x_2928_,
                            v___f_2926_,
                        );
                        return v___x_2929_;
                    }
                    1 => {
                        leanh::lean_dec_ref_known(v_info_2866_, 1);
                        leanh::lean_dec_ref(v___x_2924_);
                        leanh::lean_dec_ref(v___x_2887_);
                        v_toBind_2930_ = leanh::lean_ctor_get(v_inst_2865_, 1);
                        leanh::lean_inc_ref(v_inst_2865_);
                        leanh::lean_inc_ref(v_inst_2864_);
                        leanh::lean_inc(v_toBind_2930_);
                        v___f_2931_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13
                                as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        leanh::lean_closure_set(v___f_2931_, 0, v_resTy_2867_);
                        leanh::lean_closure_set(v___f_2931_, 1, v_k_2868_);
                        leanh::lean_closure_set(v___f_2931_, 2, v_inst_2863_);
                        leanh::lean_closure_set(v___f_2931_, 3, v_toBind_2930_);
                        leanh::lean_closure_set(v___f_2931_, 4, v_inst_2864_);
                        leanh::lean_closure_set(v___f_2931_, 5, v_inst_2865_);
                        v___x_2932_ =
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7;
                        v___x_2933_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once), _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
                        v___x_2934_ = l_Lean_Meta_withLocalDeclD___redArg(
                            v_inst_2864_,
                            v_inst_2865_,
                            v___x_2932_,
                            v___x_2933_,
                            v___f_2931_,
                        );
                        return v___x_2934_;
                    }
                    _ => {
                        v_toApplicative_2935_ = leanh::lean_ctor_get(v_inst_2865_, 0);
                        v_matcherApp_2936_ = leanh::lean_ctor_get(v_info_2866_, 0);
                        leanh::lean_inc_ref(v_matcherApp_2936_);
                        leanh::lean_dec_ref_known(v_info_2866_, 1);
                        v_toBind_2937_ = leanh::lean_ctor_get(v_inst_2865_, 1);
                        leanh::lean_inc_n(v_toBind_2937_, 3);
                        v_toPure_2938_ = leanh::lean_ctor_get(v_toApplicative_2935_, 1);
                        v_toMatcherInfo_2939_ = leanh::lean_ctor_get(v_matcherApp_2936_, 0);
                        leanh::lean_inc_ref(v_toMatcherInfo_2939_);
                        v_matcherName_2940_ = leanh::lean_ctor_get(v_matcherApp_2936_, 1);
                        leanh::lean_inc(v_matcherName_2940_);
                        v_matcherLevels_2941_ = leanh::lean_ctor_get(v_matcherApp_2936_, 2);
                        leanh::lean_inc_ref(v_matcherLevels_2941_);
                        v_params_2942_ = leanh::lean_ctor_get(v_matcherApp_2936_, 3);
                        leanh::lean_inc_ref(v_params_2942_);
                        v_motive_2943_ = leanh::lean_ctor_get(v_matcherApp_2936_, 4);
                        leanh::lean_inc_ref(v_motive_2943_);
                        v_discrs_2944_ = leanh::lean_ctor_get(v_matcherApp_2936_, 5);
                        leanh::lean_inc_ref(v_discrs_2944_);
                        v_alts_2945_ = leanh::lean_ctor_get(v_matcherApp_2936_, 6);
                        leanh::lean_inc_ref(v_alts_2945_);
                        leanh::lean_dec_ref(v_matcherApp_2936_);
                        leanh::lean_inc_ref(v_resTy_2867_);
                        v___f_2946_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed
                                as *mut core::ffi::c_void,
                            8,
                            1,
                        );
                        leanh::lean_closure_set(v___f_2946_, 0, v_resTy_2867_);
                        v___f_2947_ =
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10;
                        leanh::lean_inc(v_inst_2863_);
                        leanh::lean_inc_n(v_toPure_2938_, 2);
                        v___f_2948_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17
                                as *mut core::ffi::c_void,
                            6,
                            3,
                        );
                        leanh::lean_closure_set(v___f_2948_, 0, v_toPure_2938_);
                        leanh::lean_closure_set(v___f_2948_, 1, v_inst_2863_);
                        leanh::lean_closure_set(v___f_2948_, 2, v_toBind_2937_);
                        leanh::lean_inc_ref_n(v_inst_2865_, 2);
                        leanh::lean_inc_ref(v_inst_2864_);
                        v___f_2949_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed
                                as *mut core::ffi::c_void,
                            18,
                            17,
                        );
                        leanh::lean_closure_set(v___f_2949_, 0, v_toMatcherInfo_2939_);
                        leanh::lean_closure_set(v___f_2949_, 1, v_matcherName_2940_);
                        leanh::lean_closure_set(v___f_2949_, 2, v_params_2942_);
                        leanh::lean_closure_set(v___f_2949_, 3, v_k_2868_);
                        leanh::lean_closure_set(v___f_2949_, 4, v___x_2924_);
                        leanh::lean_closure_set(v___f_2949_, 5, v_inst_2863_);
                        leanh::lean_closure_set(v___f_2949_, 6, v_toBind_2937_);
                        leanh::lean_closure_set(v___f_2949_, 7, v___f_2947_);
                        leanh::lean_closure_set(v___f_2949_, 8, v_inst_2864_);
                        leanh::lean_closure_set(v___f_2949_, 9, v_inst_2865_);
                        leanh::lean_closure_set(v___f_2949_, 10, v_alts_2945_);
                        leanh::lean_closure_set(v___f_2949_, 11, v_toPure_2938_);
                        leanh::lean_closure_set(v___f_2949_, 12, v_matcherLevels_2941_);
                        leanh::lean_closure_set(v___f_2949_, 13, v_resTy_2867_);
                        leanh::lean_closure_set(v___f_2949_, 14, v___x_2887_);
                        leanh::lean_closure_set(v___f_2949_, 15, v_motive_2943_);
                        leanh::lean_closure_set(v___f_2949_, 16, v___f_2946_);
                        v___f_2950_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_2950_, 0, v_inst_2864_);
                        leanh::lean_closure_set(v___f_2950_, 1, v_inst_2865_);
                        leanh::lean_closure_set(v___f_2950_, 2, v___f_2949_);
                        v___x_2951_ = lean_array_get_size(v_discrs_2944_);
                        v___x_2952_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2951_);
                        v___x_2954_ = l_Array_mapFinIdxM_map___redArg(
                            v_inst_2865_,
                            v_discrs_2944_,
                            v___f_2948_,
                            v___x_2951_,
                            v___x_2952_,
                            v___x_2953_,
                        );
                        v___x_2955_ = leanh::lean_apply_4(
                            v_toBind_2937_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2954_,
                            v___f_2950_,
                        );
                        return v___x_2955_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(
    mut v_n_2962_: *mut leanh::LeanObject,
    mut v_00_u03b1_2963_: *mut leanh::LeanObject,
    mut v_inst_2964_: *mut leanh::LeanObject,
    mut v_inst_2965_: *mut leanh::LeanObject,
    mut v_inst_2966_: *mut leanh::LeanObject,
    mut v_inst_2967_: *mut leanh::LeanObject,
    mut v_info_2968_: *mut leanh::LeanObject,
    mut v_resTy_2969_: *mut leanh::LeanObject,
    mut v_k_2970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2971_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(
        v_inst_2964_,
        v_inst_2965_,
        v_inst_2966_,
        v_info_2968_,
        v_resTy_2969_,
        v_k_2970_,
    );
    return v___x_2971_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(
    mut v_n_2972_: *mut leanh::LeanObject,
    mut v_00_u03b1_2973_: *mut leanh::LeanObject,
    mut v_inst_2974_: *mut leanh::LeanObject,
    mut v_inst_2975_: *mut leanh::LeanObject,
    mut v_inst_2976_: *mut leanh::LeanObject,
    mut v_inst_2977_: *mut leanh::LeanObject,
    mut v_info_2978_: *mut leanh::LeanObject,
    mut v_resTy_2979_: *mut leanh::LeanObject,
    mut v_k_2980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2981_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(
        v_n_2972_,
        v_00_u03b1_2973_,
        v_inst_2974_,
        v_inst_2975_,
        v_inst_2976_,
        v_inst_2977_,
        v_info_2978_,
        v_resTy_2979_,
        v_k_2980_,
    );
    leanh::lean_dec(v_inst_2977_);
    return v_res_2981_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(
    mut v_u_2982_: *mut leanh::LeanObject,
    mut v_resTy_2983_: *mut leanh::LeanObject,
    mut v_c_2984_: *mut leanh::LeanObject,
    mut v_h_2985_: *mut leanh::LeanObject,
    mut v_t_2986_: *mut leanh::LeanObject,
    mut v_toPure_2987_: *mut leanh::LeanObject,
    mut v_e_2988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1;
    v___x_2990_ = leanh::lean_box(0);
    v___x_2991_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2991_, 0, v_u_2982_);
    leanh::lean_ctor_set(v___x_2991_, 1, v___x_2990_);
    v___x_2992_ = l_Lean_mkConst(v___x_2989_, v___x_2991_);
    v___x_2993_ = l_Lean_mkApp5(
        v___x_2992_,
        v_resTy_2983_,
        v_c_2984_,
        v_h_2985_,
        v_t_2986_,
        v_e_2988_,
    );
    v___x_2994_ =
        leanh::lean_apply_2(v_toPure_2987_, leanh::lean_box(0), v___x_2993_);
    return v___x_2994_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(
    mut v_u_2998_: *mut leanh::LeanObject,
    mut v_resTy_2999_: *mut leanh::LeanObject,
    mut v_c_3000_: *mut leanh::LeanObject,
    mut v_h_3001_: *mut leanh::LeanObject,
    mut v_toPure_3002_: *mut leanh::LeanObject,
    mut v_onAlt_3003_: *mut leanh::LeanObject,
    mut v___x_3004_: *mut leanh::LeanObject,
    mut v___x_3005_: *mut leanh::LeanObject,
    mut v_toBind_3006_: *mut leanh::LeanObject,
    mut v_t_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_resTy_2999_);
    v___f_3008_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_3008_, 0, v_u_2998_);
    leanh::lean_closure_set(v___f_3008_, 1, v_resTy_2999_);
    leanh::lean_closure_set(v___f_3008_, 2, v_c_3000_);
    leanh::lean_closure_set(v___f_3008_, 3, v_h_3001_);
    leanh::lean_closure_set(v___f_3008_, 4, v_t_3007_);
    leanh::lean_closure_set(v___f_3008_, 5, v_toPure_3002_);
    v___x_3009_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1;
    v___x_3010_ = leanh::lean_apply_4(
        v_onAlt_3003_,
        v___x_3009_,
        v_resTy_2999_,
        v___x_3004_,
        v___x_3005_,
    );
    v___x_3011_ = leanh::lean_apply_4(
        v_toBind_3006_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3010_,
        v___f_3008_,
    );
    return v___x_3011_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(
    mut v___x_3012_: *mut leanh::LeanObject,
    mut v_useSplitter_3013_: u8,
    mut v_inst_3014_: *mut leanh::LeanObject,
    mut v_____do__lift_3015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3016_ = 0;
    v___x_3017_ = 1;
    v___x_3018_ = leanh::lean_box((v___x_3016_) as usize);
    v___x_3019_ = leanh::lean_box((v_useSplitter_3013_) as usize);
    v___x_3020_ = leanh::lean_box((v___x_3016_) as usize);
    v___x_3021_ = leanh::lean_box((v_useSplitter_3013_) as usize);
    v___x_3022_ = leanh::lean_box((v___x_3017_) as usize);
    v___x_3023_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_3023_, 0, v___x_3012_);
    leanh::lean_closure_set(v___x_3023_, 1, v_____do__lift_3015_);
    leanh::lean_closure_set(v___x_3023_, 2, v___x_3018_);
    leanh::lean_closure_set(v___x_3023_, 3, v___x_3019_);
    leanh::lean_closure_set(v___x_3023_, 4, v___x_3020_);
    leanh::lean_closure_set(v___x_3023_, 5, v___x_3021_);
    leanh::lean_closure_set(v___x_3023_, 6, v___x_3022_);
    v___x_3024_ = leanh::lean_apply_2(v_inst_3014_, leanh::lean_box(0), v___x_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(
    mut v___x_3025_: *mut leanh::LeanObject,
    mut v_useSplitter_3026_: *mut leanh::LeanObject,
    mut v_inst_3027_: *mut leanh::LeanObject,
    mut v_____do__lift_3028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useSplitter_boxed_3029_: u8 = 0;
    let mut v_res_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3029_ = (leanh::lean_unbox(v_useSplitter_3026_) as u8);
    v_res_3030_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(
        v___x_3025_,
        v_useSplitter_boxed_3029_,
        v_inst_3027_,
        v_____do__lift_3028_,
    );
    return v_res_3030_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(
    mut v___x_3034_: *mut leanh::LeanObject,
    mut v_useSplitter_3035_: u8,
    mut v_inst_3036_: *mut leanh::LeanObject,
    mut v_onAlt_3037_: *mut leanh::LeanObject,
    mut v_resTy_3038_: *mut leanh::LeanObject,
    mut v_toBind_3039_: *mut leanh::LeanObject,
    mut v_h_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3041_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1;
    v___x_3042_ = leanh::lean_unsigned_to_nat(0);
    v___x_3043_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3044_ = lean_mk_empty_array_with_capacity(v___x_3034_);
    v___x_3045_ = lean_array_push(v___x_3044_, v_h_3040_);
    v___x_3046_ = leanh::lean_box((v_useSplitter_3035_) as usize);
    leanh::lean_inc_ref(v___x_3045_);
    v___f_3047_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3047_, 0, v___x_3045_);
    leanh::lean_closure_set(v___f_3047_, 1, v___x_3046_);
    leanh::lean_closure_set(v___f_3047_, 2, v_inst_3036_);
    v___x_3048_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3048_, 0, v___x_3043_);
    leanh::lean_ctor_set(v___x_3048_, 1, v___x_3045_);
    leanh::lean_ctor_set(v___x_3048_, 2, v___x_3043_);
    leanh::lean_ctor_set(v___x_3048_, 3, v___x_3043_);
    leanh::lean_ctor_set(v___x_3048_, 4, v___x_3043_);
    v___x_3049_ = leanh::lean_apply_4(
        v_onAlt_3037_,
        v___x_3041_,
        v_resTy_3038_,
        v___x_3042_,
        v___x_3048_,
    );
    v___x_3050_ = leanh::lean_apply_4(
        v_toBind_3039_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3049_,
        v___f_3047_,
    );
    return v___x_3050_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(
    mut v___x_3051_: *mut leanh::LeanObject,
    mut v_useSplitter_3052_: *mut leanh::LeanObject,
    mut v_inst_3053_: *mut leanh::LeanObject,
    mut v_onAlt_3054_: *mut leanh::LeanObject,
    mut v_resTy_3055_: *mut leanh::LeanObject,
    mut v_toBind_3056_: *mut leanh::LeanObject,
    mut v_h_3057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useSplitter_boxed_3058_: u8 = 0;
    let mut v_res_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3058_ = (leanh::lean_unbox(v_useSplitter_3052_) as u8);
    v_res_3059_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(
        v___x_3051_,
        v_useSplitter_boxed_3058_,
        v_inst_3053_,
        v_onAlt_3054_,
        v_resTy_3055_,
        v_toBind_3056_,
        v_h_3057_,
    );
    leanh::lean_dec(v___x_3051_);
    return v_res_3059_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(
    mut v___x_3060_: *mut leanh::LeanObject,
    mut v_useSplitter_3061_: u8,
    mut v_inst_3062_: *mut leanh::LeanObject,
    mut v_onAlt_3063_: *mut leanh::LeanObject,
    mut v_resTy_3064_: *mut leanh::LeanObject,
    mut v_toBind_3065_: *mut leanh::LeanObject,
    mut v_h_3066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3067_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1;
    v___x_3068_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3069_ = lean_mk_empty_array_with_capacity(v___x_3060_);
    v___x_3070_ = lean_array_push(v___x_3069_, v_h_3066_);
    v___x_3071_ = leanh::lean_box((v_useSplitter_3061_) as usize);
    leanh::lean_inc_ref(v___x_3070_);
    v___f_3072_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3072_, 0, v___x_3070_);
    leanh::lean_closure_set(v___f_3072_, 1, v___x_3071_);
    leanh::lean_closure_set(v___f_3072_, 2, v_inst_3062_);
    v___x_3073_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3073_, 0, v___x_3068_);
    leanh::lean_ctor_set(v___x_3073_, 1, v___x_3070_);
    leanh::lean_ctor_set(v___x_3073_, 2, v___x_3068_);
    leanh::lean_ctor_set(v___x_3073_, 3, v___x_3068_);
    leanh::lean_ctor_set(v___x_3073_, 4, v___x_3068_);
    v___x_3074_ = leanh::lean_apply_4(
        v_onAlt_3063_,
        v___x_3067_,
        v_resTy_3064_,
        v___x_3060_,
        v___x_3073_,
    );
    v___x_3075_ = leanh::lean_apply_4(
        v_toBind_3065_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3074_,
        v___f_3072_,
    );
    return v___x_3075_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(
    mut v___x_3076_: *mut leanh::LeanObject,
    mut v_useSplitter_3077_: *mut leanh::LeanObject,
    mut v_inst_3078_: *mut leanh::LeanObject,
    mut v_onAlt_3079_: *mut leanh::LeanObject,
    mut v_resTy_3080_: *mut leanh::LeanObject,
    mut v_toBind_3081_: *mut leanh::LeanObject,
    mut v_h_3082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useSplitter_boxed_3083_: u8 = 0;
    let mut v_res_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3083_ = (leanh::lean_unbox(v_useSplitter_3077_) as u8);
    v_res_3084_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(
        v___x_3076_,
        v_useSplitter_boxed_3083_,
        v_inst_3078_,
        v_onAlt_3079_,
        v_resTy_3080_,
        v_toBind_3081_,
        v_h_3082_,
    );
    return v_res_3084_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(
    mut v_u_3085_: *mut leanh::LeanObject,
    mut v_resTy_3086_: *mut leanh::LeanObject,
    mut v_c_3087_: *mut leanh::LeanObject,
    mut v_h_3088_: *mut leanh::LeanObject,
    mut v_t_3089_: *mut leanh::LeanObject,
    mut v_toPure_3090_: *mut leanh::LeanObject,
    mut v_e_3091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3092_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1;
    v___x_3093_ = leanh::lean_box(0);
    v___x_3094_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3094_, 0, v_u_3085_);
    leanh::lean_ctor_set(v___x_3094_, 1, v___x_3093_);
    v___x_3095_ = l_Lean_mkConst(v___x_3092_, v___x_3094_);
    v___x_3096_ = l_Lean_mkApp5(
        v___x_3095_,
        v_resTy_3086_,
        v_c_3087_,
        v_h_3088_,
        v_t_3089_,
        v_e_3091_,
    );
    v___x_3097_ =
        leanh::lean_apply_2(v_toPure_3090_, leanh::lean_box(0), v___x_3096_);
    return v___x_3097_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(
    mut v_u_3098_: *mut leanh::LeanObject,
    mut v_resTy_3099_: *mut leanh::LeanObject,
    mut v_c_3100_: *mut leanh::LeanObject,
    mut v_h_3101_: *mut leanh::LeanObject,
    mut v_toPure_3102_: *mut leanh::LeanObject,
    mut v_inst_3103_: *mut leanh::LeanObject,
    mut v_inst_3104_: *mut leanh::LeanObject,
    mut v_n_3105_: *mut leanh::LeanObject,
    mut v___x_3106_: u8,
    mut v___f_3107_: *mut leanh::LeanObject,
    mut v___x_3108_: u8,
    mut v_toBind_3109_: *mut leanh::LeanObject,
    mut v_t_3110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_c_3100_);
    v___f_3111_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_3111_, 0, v_u_3098_);
    leanh::lean_closure_set(v___f_3111_, 1, v_resTy_3099_);
    leanh::lean_closure_set(v___f_3111_, 2, v_c_3100_);
    leanh::lean_closure_set(v___f_3111_, 3, v_h_3101_);
    leanh::lean_closure_set(v___f_3111_, 4, v_t_3110_);
    leanh::lean_closure_set(v___f_3111_, 5, v_toPure_3102_);
    v___x_3112_ = l_Lean_mkNot(v_c_3100_);
    v___x_3113_ = l_Lean_Meta_withLocalDecl___redArg(
        v_inst_3103_,
        v_inst_3104_,
        v_n_3105_,
        v___x_3106_,
        v___x_3112_,
        v___f_3107_,
        v___x_3108_,
    );
    v___x_3114_ = leanh::lean_apply_4(
        v_toBind_3109_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3113_,
        v___f_3111_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(
    mut v_u_3115_: *mut leanh::LeanObject,
    mut v_resTy_3116_: *mut leanh::LeanObject,
    mut v_c_3117_: *mut leanh::LeanObject,
    mut v_h_3118_: *mut leanh::LeanObject,
    mut v_toPure_3119_: *mut leanh::LeanObject,
    mut v_inst_3120_: *mut leanh::LeanObject,
    mut v_inst_3121_: *mut leanh::LeanObject,
    mut v_n_3122_: *mut leanh::LeanObject,
    mut v___x_3123_: *mut leanh::LeanObject,
    mut v___f_3124_: *mut leanh::LeanObject,
    mut v___x_3125_: *mut leanh::LeanObject,
    mut v_toBind_3126_: *mut leanh::LeanObject,
    mut v_t_3127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1249__boxed_3128_: u8 = 0;
    let mut v___x_1251__boxed_3129_: u8 = 0;
    let mut v_res_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1249__boxed_3128_ = (leanh::lean_unbox(v___x_3123_) as u8);
    v___x_1251__boxed_3129_ = (leanh::lean_unbox(v___x_3125_) as u8);
    v_res_3130_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(
        v_u_3115_,
        v_resTy_3116_,
        v_c_3117_,
        v_h_3118_,
        v_toPure_3119_,
        v_inst_3120_,
        v_inst_3121_,
        v_n_3122_,
        v___x_1249__boxed_3128_,
        v___f_3124_,
        v___x_1251__boxed_3129_,
        v_toBind_3126_,
        v_t_3127_,
    );
    return v_res_3130_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(
    mut v_u_3131_: *mut leanh::LeanObject,
    mut v_resTy_3132_: *mut leanh::LeanObject,
    mut v_c_3133_: *mut leanh::LeanObject,
    mut v_h_3134_: *mut leanh::LeanObject,
    mut v_toPure_3135_: *mut leanh::LeanObject,
    mut v_inst_3136_: *mut leanh::LeanObject,
    mut v_inst_3137_: *mut leanh::LeanObject,
    mut v___f_3138_: *mut leanh::LeanObject,
    mut v_toBind_3139_: *mut leanh::LeanObject,
    mut v___f_3140_: *mut leanh::LeanObject,
    mut v_n_3141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3142_: u8 = 0;
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3142_ = 0;
    v___x_3143_ = 0;
    v___x_3144_ = leanh::lean_box((v___x_3142_) as usize);
    v___x_3145_ = leanh::lean_box((v___x_3143_) as usize);
    leanh::lean_inc(v_toBind_3139_);
    leanh::lean_inc(v_n_3141_);
    leanh::lean_inc_ref(v_inst_3137_);
    leanh::lean_inc_ref(v_inst_3136_);
    leanh::lean_inc_ref(v_c_3133_);
    v___f_3146_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        13,
        12,
    );
    leanh::lean_closure_set(v___f_3146_, 0, v_u_3131_);
    leanh::lean_closure_set(v___f_3146_, 1, v_resTy_3132_);
    leanh::lean_closure_set(v___f_3146_, 2, v_c_3133_);
    leanh::lean_closure_set(v___f_3146_, 3, v_h_3134_);
    leanh::lean_closure_set(v___f_3146_, 4, v_toPure_3135_);
    leanh::lean_closure_set(v___f_3146_, 5, v_inst_3136_);
    leanh::lean_closure_set(v___f_3146_, 6, v_inst_3137_);
    leanh::lean_closure_set(v___f_3146_, 7, v_n_3141_);
    leanh::lean_closure_set(v___f_3146_, 8, v___x_3144_);
    leanh::lean_closure_set(v___f_3146_, 9, v___f_3138_);
    leanh::lean_closure_set(v___f_3146_, 10, v___x_3145_);
    leanh::lean_closure_set(v___f_3146_, 11, v_toBind_3139_);
    v___x_3147_ = l_Lean_Meta_withLocalDecl___redArg(
        v_inst_3136_,
        v_inst_3137_,
        v_n_3141_,
        v___x_3142_,
        v_c_3133_,
        v___f_3140_,
        v___x_3143_,
    );
    v___x_3148_ = leanh::lean_apply_4(
        v_toBind_3139_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3147_,
        v___f_3146_,
    );
    return v___x_3148_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(
    mut v___x_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
    mut v___y_3153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Lean_Core_mkFreshUserName(v___x_3149_, v___y_3152_, v___y_3153_);
    return v___x_3155_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(
    mut v___x_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
    mut v___y_3158_: *mut leanh::LeanObject,
    mut v___y_3159_: *mut leanh::LeanObject,
    mut v___y_3160_: *mut leanh::LeanObject,
    mut v___y_3161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3162_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(
        v___x_3156_,
        v___y_3157_,
        v___y_3158_,
        v___y_3159_,
        v___y_3160_,
    );
    leanh::lean_dec(v___y_3160_);
    leanh::lean_dec_ref(v___y_3159_);
    leanh::lean_dec(v___y_3158_);
    leanh::lean_dec_ref(v___y_3157_);
    return v_res_3162_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(
    mut v_e_3170_: *mut leanh::LeanObject,
    mut v_useSplitter_3171_: u8,
    mut v_resTy_3172_: *mut leanh::LeanObject,
    mut v_toPure_3173_: *mut leanh::LeanObject,
    mut v_onAlt_3174_: *mut leanh::LeanObject,
    mut v_toBind_3175_: *mut leanh::LeanObject,
    mut v_inst_3176_: *mut leanh::LeanObject,
    mut v_inst_3177_: *mut leanh::LeanObject,
    mut v_inst_3178_: *mut leanh::LeanObject,
    mut v_u_3179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3180_ = leanh::lean_unsigned_to_nat(1);
    v___x_3181_ = l_Lean_Expr_getAppNumArgs(v_e_3170_);
    v___x_3182_ = lean_nat_sub(v___x_3181_, v___x_3180_);
    v___x_3183_ = lean_nat_sub(v___x_3182_, v___x_3180_);
    leanh::lean_dec(v___x_3182_);
    v_c_3184_ = l_Lean_Expr_getRevArg_x21(v_e_3170_, v___x_3183_);
    v___x_3185_ = leanh::lean_unsigned_to_nat(2);
    v___x_3186_ = lean_nat_sub(v___x_3181_, v___x_3185_);
    leanh::lean_dec(v___x_3181_);
    v___x_3187_ = lean_nat_sub(v___x_3186_, v___x_3180_);
    leanh::lean_dec(v___x_3186_);
    v_h_3188_ = l_Lean_Expr_getRevArg_x21(v_e_3170_, v___x_3187_);
    if v_useSplitter_3171_ == 0 {
        let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_3178_);
        leanh::lean_dec_ref(v_inst_3177_);
        leanh::lean_dec(v_inst_3176_);
        v___x_3189_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1;
        v___x_3190_ = leanh::lean_unsigned_to_nat(0);
        v___x_3191_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0;
        leanh::lean_inc(v_toBind_3175_);
        leanh::lean_inc(v_onAlt_3174_);
        leanh::lean_inc_ref(v_resTy_3172_);
        v___f_3192_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1 as *mut core::ffi::c_void,
            10,
            9,
        );
        leanh::lean_closure_set(v___f_3192_, 0, v_u_3179_);
        leanh::lean_closure_set(v___f_3192_, 1, v_resTy_3172_);
        leanh::lean_closure_set(v___f_3192_, 2, v_c_3184_);
        leanh::lean_closure_set(v___f_3192_, 3, v_h_3188_);
        leanh::lean_closure_set(v___f_3192_, 4, v_toPure_3173_);
        leanh::lean_closure_set(v___f_3192_, 5, v_onAlt_3174_);
        leanh::lean_closure_set(v___f_3192_, 6, v___x_3180_);
        leanh::lean_closure_set(v___f_3192_, 7, v___x_3191_);
        leanh::lean_closure_set(v___f_3192_, 8, v_toBind_3175_);
        v___x_3193_ = leanh::lean_apply_4(
            v_onAlt_3174_,
            v___x_3189_,
            v_resTy_3172_,
            v___x_3190_,
            v___x_3191_,
        );
        v___x_3194_ = leanh::lean_apply_4(
            v_toBind_3175_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3193_,
            v___f_3192_,
        );
        return v___x_3194_;
    } else {
        let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3195_ = leanh::lean_box((v_useSplitter_3171_) as usize);
        leanh::lean_inc_n(v_toBind_3175_, 3);
        leanh::lean_inc_ref_n(v_resTy_3172_, 2);
        leanh::lean_inc(v_onAlt_3174_);
        leanh::lean_inc_n(v_inst_3176_, 2);
        v___f_3196_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed
                as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_3196_, 0, v___x_3180_);
        leanh::lean_closure_set(v___f_3196_, 1, v___x_3195_);
        leanh::lean_closure_set(v___f_3196_, 2, v_inst_3176_);
        leanh::lean_closure_set(v___f_3196_, 3, v_onAlt_3174_);
        leanh::lean_closure_set(v___f_3196_, 4, v_resTy_3172_);
        leanh::lean_closure_set(v___f_3196_, 5, v_toBind_3175_);
        v___x_3197_ = leanh::lean_box((v_useSplitter_3171_) as usize);
        v___f_3198_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed
                as *mut core::ffi::c_void,
            7,
            6,
        );
        leanh::lean_closure_set(v___f_3198_, 0, v___x_3180_);
        leanh::lean_closure_set(v___f_3198_, 1, v___x_3197_);
        leanh::lean_closure_set(v___f_3198_, 2, v_inst_3176_);
        leanh::lean_closure_set(v___f_3198_, 3, v_onAlt_3174_);
        leanh::lean_closure_set(v___f_3198_, 4, v_resTy_3172_);
        leanh::lean_closure_set(v___f_3198_, 5, v_toBind_3175_);
        v___f_3199_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7 as *mut core::ffi::c_void,
            11,
            10,
        );
        leanh::lean_closure_set(v___f_3199_, 0, v_u_3179_);
        leanh::lean_closure_set(v___f_3199_, 1, v_resTy_3172_);
        leanh::lean_closure_set(v___f_3199_, 2, v_c_3184_);
        leanh::lean_closure_set(v___f_3199_, 3, v_h_3188_);
        leanh::lean_closure_set(v___f_3199_, 4, v_toPure_3173_);
        leanh::lean_closure_set(v___f_3199_, 5, v_inst_3177_);
        leanh::lean_closure_set(v___f_3199_, 6, v_inst_3178_);
        leanh::lean_closure_set(v___f_3199_, 7, v___f_3198_);
        leanh::lean_closure_set(v___f_3199_, 8, v_toBind_3175_);
        leanh::lean_closure_set(v___f_3199_, 9, v___f_3196_);
        v___f_3200_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3;
        v___x_3201_ =
            leanh::lean_apply_2(v_inst_3176_, leanh::lean_box(0), v___f_3200_);
        v___x_3202_ = leanh::lean_apply_4(
            v_toBind_3175_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3201_,
            v___f_3199_,
        );
        return v___x_3202_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(
    mut v_e_3203_: *mut leanh::LeanObject,
    mut v_useSplitter_3204_: *mut leanh::LeanObject,
    mut v_resTy_3205_: *mut leanh::LeanObject,
    mut v_toPure_3206_: *mut leanh::LeanObject,
    mut v_onAlt_3207_: *mut leanh::LeanObject,
    mut v_toBind_3208_: *mut leanh::LeanObject,
    mut v_inst_3209_: *mut leanh::LeanObject,
    mut v_inst_3210_: *mut leanh::LeanObject,
    mut v_inst_3211_: *mut leanh::LeanObject,
    mut v_u_3212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useSplitter_boxed_3213_: u8 = 0;
    let mut v_res_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3213_ = (leanh::lean_unbox(v_useSplitter_3204_) as u8);
    v_res_3214_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(
        v_e_3203_,
        v_useSplitter_boxed_3213_,
        v_resTy_3205_,
        v_toPure_3206_,
        v_onAlt_3207_,
        v_toBind_3208_,
        v_inst_3209_,
        v_inst_3210_,
        v_inst_3211_,
        v_u_3212_,
    );
    leanh::lean_dec_ref(v_e_3203_);
    return v_res_3214_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(
    mut v___x_3215_: *mut leanh::LeanObject,
    mut v_inst_3216_: *mut leanh::LeanObject,
    mut v_____do__lift_3217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3218_ = 0;
    v___x_3219_ = 1;
    v___x_3220_ = 1;
    v___x_3221_ = leanh::lean_box((v___x_3218_) as usize);
    v___x_3222_ = leanh::lean_box((v___x_3219_) as usize);
    v___x_3223_ = leanh::lean_box((v___x_3218_) as usize);
    v___x_3224_ = leanh::lean_box((v___x_3219_) as usize);
    v___x_3225_ = leanh::lean_box((v___x_3220_) as usize);
    v___x_3226_ = leanh::lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    leanh::lean_closure_set(v___x_3226_, 0, v___x_3215_);
    leanh::lean_closure_set(v___x_3226_, 1, v_____do__lift_3217_);
    leanh::lean_closure_set(v___x_3226_, 2, v___x_3221_);
    leanh::lean_closure_set(v___x_3226_, 3, v___x_3222_);
    leanh::lean_closure_set(v___x_3226_, 4, v___x_3223_);
    leanh::lean_closure_set(v___x_3226_, 5, v___x_3224_);
    leanh::lean_closure_set(v___x_3226_, 6, v___x_3225_);
    v___x_3227_ = leanh::lean_apply_2(v_inst_3216_, leanh::lean_box(0), v___x_3226_);
    return v___x_3227_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(
    mut v_inst_3228_: *mut leanh::LeanObject,
    mut v_onAlt_3229_: *mut leanh::LeanObject,
    mut v_resTy_3230_: *mut leanh::LeanObject,
    mut v_toBind_3231_: *mut leanh::LeanObject,
    mut v_h_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1;
    v___x_3234_ = leanh::lean_unsigned_to_nat(0);
    v___x_3235_ = leanh::lean_unsigned_to_nat(1);
    v___x_3236_ = lean_mk_empty_array_with_capacity(v___x_3235_);
    v___x_3237_ = lean_array_push(v___x_3236_, v_h_3232_);
    leanh::lean_inc_ref_n(v___x_3237_, 2);
    v___f_3238_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3238_, 0, v___x_3237_);
    leanh::lean_closure_set(v___f_3238_, 1, v_inst_3228_);
    v___x_3239_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3240_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3240_, 0, v___x_3237_);
    leanh::lean_ctor_set(v___x_3240_, 1, v___x_3237_);
    leanh::lean_ctor_set(v___x_3240_, 2, v___x_3239_);
    leanh::lean_ctor_set(v___x_3240_, 3, v___x_3239_);
    leanh::lean_ctor_set(v___x_3240_, 4, v___x_3239_);
    v___x_3241_ = leanh::lean_apply_4(
        v_onAlt_3229_,
        v___x_3233_,
        v_resTy_3230_,
        v___x_3234_,
        v___x_3240_,
    );
    v___x_3242_ = leanh::lean_apply_4(
        v_toBind_3231_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3241_,
        v___f_3238_,
    );
    return v___x_3242_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(
    mut v___x_3243_: *mut leanh::LeanObject,
    mut v_inst_3244_: *mut leanh::LeanObject,
    mut v_onAlt_3245_: *mut leanh::LeanObject,
    mut v_resTy_3246_: *mut leanh::LeanObject,
    mut v_toBind_3247_: *mut leanh::LeanObject,
    mut v_h_3248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3249_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1;
    v___x_3250_ = lean_mk_empty_array_with_capacity(v___x_3243_);
    v___x_3251_ = lean_array_push(v___x_3250_, v_h_3248_);
    leanh::lean_inc_ref_n(v___x_3251_, 2);
    v___f_3252_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3252_, 0, v___x_3251_);
    leanh::lean_closure_set(v___f_3252_, 1, v_inst_3244_);
    v___x_3253_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3254_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3254_, 0, v___x_3251_);
    leanh::lean_ctor_set(v___x_3254_, 1, v___x_3251_);
    leanh::lean_ctor_set(v___x_3254_, 2, v___x_3253_);
    leanh::lean_ctor_set(v___x_3254_, 3, v___x_3253_);
    leanh::lean_ctor_set(v___x_3254_, 4, v___x_3253_);
    v___x_3255_ = leanh::lean_apply_4(
        v_onAlt_3245_,
        v___x_3249_,
        v_resTy_3246_,
        v___x_3243_,
        v___x_3254_,
    );
    v___x_3256_ = leanh::lean_apply_4(
        v_toBind_3247_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3255_,
        v___f_3252_,
    );
    return v___x_3256_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(
    mut v_inst_3257_: *mut leanh::LeanObject,
    mut v_onAlt_3258_: *mut leanh::LeanObject,
    mut v_resTy_3259_: *mut leanh::LeanObject,
    mut v_toBind_3260_: *mut leanh::LeanObject,
    mut v_e_3261_: *mut leanh::LeanObject,
    mut v_toPure_3262_: *mut leanh::LeanObject,
    mut v_inst_3263_: *mut leanh::LeanObject,
    mut v_inst_3264_: *mut leanh::LeanObject,
    mut v___f_3265_: *mut leanh::LeanObject,
    mut v_u_3266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3267_ = leanh::lean_unsigned_to_nat(1);
    leanh::lean_inc_n(v_toBind_3260_, 2);
    leanh::lean_inc_ref(v_resTy_3259_);
    leanh::lean_inc(v_inst_3257_);
    v___f_3268_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13 as *mut core::ffi::c_void,
        6,
        5,
    );
    leanh::lean_closure_set(v___f_3268_, 0, v___x_3267_);
    leanh::lean_closure_set(v___f_3268_, 1, v_inst_3257_);
    leanh::lean_closure_set(v___f_3268_, 2, v_onAlt_3258_);
    leanh::lean_closure_set(v___f_3268_, 3, v_resTy_3259_);
    leanh::lean_closure_set(v___f_3268_, 4, v_toBind_3260_);
    v___x_3269_ = l_Lean_Expr_getAppNumArgs(v_e_3261_);
    v___x_3270_ = lean_nat_sub(v___x_3269_, v___x_3267_);
    v___x_3271_ = lean_nat_sub(v___x_3270_, v___x_3267_);
    leanh::lean_dec(v___x_3270_);
    v_c_3272_ = l_Lean_Expr_getRevArg_x21(v_e_3261_, v___x_3271_);
    v___x_3273_ = leanh::lean_unsigned_to_nat(2);
    v___x_3274_ = lean_nat_sub(v___x_3269_, v___x_3273_);
    leanh::lean_dec(v___x_3269_);
    v___x_3275_ = lean_nat_sub(v___x_3274_, v___x_3267_);
    leanh::lean_dec(v___x_3274_);
    v_h_3276_ = l_Lean_Expr_getRevArg_x21(v_e_3261_, v___x_3275_);
    v___f_3277_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7 as *mut core::ffi::c_void,
        11,
        10,
    );
    leanh::lean_closure_set(v___f_3277_, 0, v_u_3266_);
    leanh::lean_closure_set(v___f_3277_, 1, v_resTy_3259_);
    leanh::lean_closure_set(v___f_3277_, 2, v_c_3272_);
    leanh::lean_closure_set(v___f_3277_, 3, v_h_3276_);
    leanh::lean_closure_set(v___f_3277_, 4, v_toPure_3262_);
    leanh::lean_closure_set(v___f_3277_, 5, v_inst_3263_);
    leanh::lean_closure_set(v___f_3277_, 6, v_inst_3264_);
    leanh::lean_closure_set(v___f_3277_, 7, v___f_3268_);
    leanh::lean_closure_set(v___f_3277_, 8, v_toBind_3260_);
    leanh::lean_closure_set(v___f_3277_, 9, v___f_3265_);
    v___f_3278_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3;
    v___x_3279_ = leanh::lean_apply_2(v_inst_3257_, leanh::lean_box(0), v___f_3278_);
    v___x_3280_ = leanh::lean_apply_4(
        v_toBind_3260_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3279_,
        v___f_3277_,
    );
    return v___x_3280_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(
    mut v_inst_3281_: *mut leanh::LeanObject,
    mut v_onAlt_3282_: *mut leanh::LeanObject,
    mut v_resTy_3283_: *mut leanh::LeanObject,
    mut v_toBind_3284_: *mut leanh::LeanObject,
    mut v_e_3285_: *mut leanh::LeanObject,
    mut v_toPure_3286_: *mut leanh::LeanObject,
    mut v_inst_3287_: *mut leanh::LeanObject,
    mut v_inst_3288_: *mut leanh::LeanObject,
    mut v___f_3289_: *mut leanh::LeanObject,
    mut v_u_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3291_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(
        v_inst_3281_,
        v_onAlt_3282_,
        v_resTy_3283_,
        v_toBind_3284_,
        v_e_3285_,
        v_toPure_3286_,
        v_inst_3287_,
        v_inst_3288_,
        v___f_3289_,
        v_u_3290_,
    );
    leanh::lean_dec_ref(v_e_3285_);
    return v_res_3291_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(
    mut v_onAlt_3292_: *mut leanh::LeanObject,
    mut v_idx_3293_: *mut leanh::LeanObject,
    mut v_expAltType_3294_: *mut leanh::LeanObject,
    mut v_altFVars_3295_: *mut leanh::LeanObject,
    mut v___alt_3296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3297_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2;
    v___x_3298_ = leanh::lean_unsigned_to_nat(1);
    v___x_3299_ = lean_nat_add(v_idx_3293_, v___x_3298_);
    v___x_3300_ = lean_name_append_index_after(v___x_3297_, v___x_3299_);
    v___x_3301_ = leanh::lean_apply_4(
        v_onAlt_3292_,
        v___x_3300_,
        v_expAltType_3294_,
        v_idx_3293_,
        v_altFVars_3295_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(
    mut v_onAlt_3302_: *mut leanh::LeanObject,
    mut v_idx_3303_: *mut leanh::LeanObject,
    mut v_expAltType_3304_: *mut leanh::LeanObject,
    mut v_altFVars_3305_: *mut leanh::LeanObject,
    mut v___alt_3306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(
        v_onAlt_3302_,
        v_idx_3303_,
        v_expAltType_3304_,
        v_altFVars_3305_,
        v___alt_3306_,
    );
    leanh::lean_dec_ref(v___alt_3306_);
    return v_res_3307_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(
    mut v_mask_3308_: *mut leanh::LeanObject,
    mut v_absMotiveBody_3309_: *mut leanh::LeanObject,
    mut v_toPure_3310_: *mut leanh::LeanObject,
    mut v_xs_3311_: *mut leanh::LeanObject,
    mut v___body_3312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = l_Array_mask___redArg(v_mask_3308_, v_xs_3311_);
    v___x_3314_ = lean_expr_instantiate_rev(v_absMotiveBody_3309_, v___x_3313_);
    leanh::lean_dec(v___x_3313_);
    v___x_3315_ =
        leanh::lean_apply_2(v_toPure_3310_, leanh::lean_box(0), v___x_3314_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(
    mut v_mask_3316_: *mut leanh::LeanObject,
    mut v_absMotiveBody_3317_: *mut leanh::LeanObject,
    mut v_toPure_3318_: *mut leanh::LeanObject,
    mut v_xs_3319_: *mut leanh::LeanObject,
    mut v___body_3320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(
        v_mask_3316_,
        v_absMotiveBody_3317_,
        v_toPure_3318_,
        v_xs_3319_,
        v___body_3320_,
    );
    leanh::lean_dec_ref(v___body_3320_);
    leanh::lean_dec_ref(v_absMotiveBody_3317_);
    leanh::lean_dec_ref(v_mask_3316_);
    return v_res_3321_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(
    mut v_toFunctor_3322_: *mut leanh::LeanObject,
    mut v_mask_3323_: *mut leanh::LeanObject,
    mut v_toPure_3324_: *mut leanh::LeanObject,
    mut v_inst_3325_: *mut leanh::LeanObject,
    mut v_inst_3326_: *mut leanh::LeanObject,
    mut v_inst_3327_: *mut leanh::LeanObject,
    mut v_inst_3328_: *mut leanh::LeanObject,
    mut v_inst_3329_: *mut leanh::LeanObject,
    mut v_matcherApp_3330_: *mut leanh::LeanObject,
    mut v_useSplitter_3331_: u8,
    mut v___f_3332_: *mut leanh::LeanObject,
    mut v___f_3333_: *mut leanh::LeanObject,
    mut v_absMotiveBody_3334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_3335_ = leanh::lean_ctor_get(v_toFunctor_3322_, 0);
    leanh::lean_inc(v_map_3335_);
    leanh::lean_dec_ref(v_toFunctor_3322_);
    leanh::lean_inc(v_toPure_3324_);
    v___f_3336_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_3336_, 0, v_mask_3323_);
    leanh::lean_closure_set(v___f_3336_, 1, v_absMotiveBody_3334_);
    leanh::lean_closure_set(v___f_3336_, 2, v_toPure_3324_);
    v___x_3337_ = leanh::lean_apply_1(v_toPure_3324_, leanh::lean_box(0));
    leanh::lean_inc(v___x_3337_);
    v___x_3338_ = l_Lean_Meta_MatcherApp_transform___redArg(
        v_inst_3325_,
        v_inst_3326_,
        v_inst_3327_,
        v_inst_3328_,
        v_inst_3329_,
        v_matcherApp_3330_,
        v_useSplitter_3331_,
        v_useSplitter_3331_,
        v___x_3337_,
        v___f_3336_,
        v___f_3332_,
        v___x_3337_,
    );
    v___x_3339_ = leanh::lean_apply_4(
        v_map_3335_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_3333_,
        v___x_3338_,
    );
    return v___x_3339_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(
    mut v_toFunctor_3340_: *mut leanh::LeanObject,
    mut v_mask_3341_: *mut leanh::LeanObject,
    mut v_toPure_3342_: *mut leanh::LeanObject,
    mut v_inst_3343_: *mut leanh::LeanObject,
    mut v_inst_3344_: *mut leanh::LeanObject,
    mut v_inst_3345_: *mut leanh::LeanObject,
    mut v_inst_3346_: *mut leanh::LeanObject,
    mut v_inst_3347_: *mut leanh::LeanObject,
    mut v_matcherApp_3348_: *mut leanh::LeanObject,
    mut v_useSplitter_3349_: *mut leanh::LeanObject,
    mut v___f_3350_: *mut leanh::LeanObject,
    mut v___f_3351_: *mut leanh::LeanObject,
    mut v_absMotiveBody_3352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useSplitter_boxed_3353_: u8 = 0;
    let mut v_res_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3353_ = (leanh::lean_unbox(v_useSplitter_3349_) as u8);
    v_res_3354_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(
        v_toFunctor_3340_,
        v_mask_3341_,
        v_toPure_3342_,
        v_inst_3343_,
        v_inst_3344_,
        v_inst_3345_,
        v_inst_3346_,
        v_inst_3347_,
        v_matcherApp_3348_,
        v_useSplitter_boxed_3353_,
        v___f_3350_,
        v___f_3351_,
        v_absMotiveBody_3352_,
    );
    return v_res_3354_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(
    mut v_inst_3357_: *mut leanh::LeanObject,
    mut v_inst_3358_: *mut leanh::LeanObject,
    mut v_inst_3359_: *mut leanh::LeanObject,
    mut v_inst_3360_: *mut leanh::LeanObject,
    mut v_inst_3361_: *mut leanh::LeanObject,
    mut v_info_3362_: *mut leanh::LeanObject,
    mut v_resTy_3363_: *mut leanh::LeanObject,
    mut v_onAlt_3364_: *mut leanh::LeanObject,
    mut v_useSplitter_3365_: u8,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_info_3362_) {
        0 => {
            let mut v_toApplicative_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_3366_ = leanh::lean_ctor_get(v_inst_3359_, 0);
            leanh::lean_dec_ref(v_inst_3361_);
            leanh::lean_dec_ref(v_inst_3360_);
            v_toBind_3367_ = leanh::lean_ctor_get(v_inst_3359_, 1);
            leanh::lean_inc_n(v_toBind_3367_, 2);
            v_toPure_3368_ = leanh::lean_ctor_get(v_toApplicative_3366_, 1);
            leanh::lean_inc(v_toPure_3368_);
            v_e_3369_ = leanh::lean_ctor_get(v_info_3362_, 0);
            leanh::lean_inc_ref(v_e_3369_);
            leanh::lean_dec_ref_known(v_info_3362_, 1);
            v___x_3370_ = leanh::lean_box((v_useSplitter_3365_) as usize);
            leanh::lean_inc(v_inst_3357_);
            leanh::lean_inc_ref(v_resTy_3363_);
            v___f_3371_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            leanh::lean_closure_set(v___f_3371_, 0, v_e_3369_);
            leanh::lean_closure_set(v___f_3371_, 1, v___x_3370_);
            leanh::lean_closure_set(v___f_3371_, 2, v_resTy_3363_);
            leanh::lean_closure_set(v___f_3371_, 3, v_toPure_3368_);
            leanh::lean_closure_set(v___f_3371_, 4, v_onAlt_3364_);
            leanh::lean_closure_set(v___f_3371_, 5, v_toBind_3367_);
            leanh::lean_closure_set(v___f_3371_, 6, v_inst_3357_);
            leanh::lean_closure_set(v___f_3371_, 7, v_inst_3358_);
            leanh::lean_closure_set(v___f_3371_, 8, v_inst_3359_);
            v___x_3372_ = leanh::lean_alloc_closure(
                l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void,
                6,
                1,
            );
            leanh::lean_closure_set(v___x_3372_, 0, v_resTy_3363_);
            v___x_3373_ =
                leanh::lean_apply_2(v_inst_3357_, leanh::lean_box(0), v___x_3372_);
            v___x_3374_ = leanh::lean_apply_4(
                v_toBind_3367_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3373_,
                v___f_3371_,
            );
            return v___x_3374_;
        }
        1 => {
            let mut v_toApplicative_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_e_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_3375_ = leanh::lean_ctor_get(v_inst_3359_, 0);
            leanh::lean_dec_ref(v_inst_3361_);
            leanh::lean_dec_ref(v_inst_3360_);
            v_toBind_3376_ = leanh::lean_ctor_get(v_inst_3359_, 1);
            leanh::lean_inc_n(v_toBind_3376_, 3);
            v_toPure_3377_ = leanh::lean_ctor_get(v_toApplicative_3375_, 1);
            leanh::lean_inc(v_toPure_3377_);
            v_e_3378_ = leanh::lean_ctor_get(v_info_3362_, 0);
            leanh::lean_inc_ref(v_e_3378_);
            leanh::lean_dec_ref_known(v_info_3362_, 1);
            leanh::lean_inc_ref_n(v_resTy_3363_, 2);
            leanh::lean_inc(v_onAlt_3364_);
            leanh::lean_inc_n(v_inst_3357_, 2);
            v___f_3379_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            leanh::lean_closure_set(v___f_3379_, 0, v_inst_3357_);
            leanh::lean_closure_set(v___f_3379_, 1, v_onAlt_3364_);
            leanh::lean_closure_set(v___f_3379_, 2, v_resTy_3363_);
            leanh::lean_closure_set(v___f_3379_, 3, v_toBind_3376_);
            v___f_3380_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            leanh::lean_closure_set(v___f_3380_, 0, v_inst_3357_);
            leanh::lean_closure_set(v___f_3380_, 1, v_onAlt_3364_);
            leanh::lean_closure_set(v___f_3380_, 2, v_resTy_3363_);
            leanh::lean_closure_set(v___f_3380_, 3, v_toBind_3376_);
            leanh::lean_closure_set(v___f_3380_, 4, v_e_3378_);
            leanh::lean_closure_set(v___f_3380_, 5, v_toPure_3377_);
            leanh::lean_closure_set(v___f_3380_, 6, v_inst_3358_);
            leanh::lean_closure_set(v___f_3380_, 7, v_inst_3359_);
            leanh::lean_closure_set(v___f_3380_, 8, v___f_3379_);
            v___x_3381_ = leanh::lean_alloc_closure(
                l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void,
                6,
                1,
            );
            leanh::lean_closure_set(v___x_3381_, 0, v_resTy_3363_);
            v___x_3382_ =
                leanh::lean_apply_2(v_inst_3357_, leanh::lean_box(0), v___x_3381_);
            v___x_3383_ = leanh::lean_apply_4(
                v_toBind_3376_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3382_,
                v___f_3380_,
            );
            return v___x_3383_;
        }
        _ => {
            let mut v_toApplicative_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_matcherApp_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toFunctor_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_discrs_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_sz_3394_: usize = 0;
            let mut v___x_3395_: usize = 0;
            let mut v_mask_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_maskedDiscrs_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_3384_ = leanh::lean_ctor_get(v_inst_3359_, 0);
            v_matcherApp_3385_ = leanh::lean_ctor_get(v_info_3362_, 0);
            leanh::lean_inc_ref(v_matcherApp_3385_);
            leanh::lean_dec_ref_known(v_info_3362_, 1);
            v_toBind_3386_ = leanh::lean_ctor_get(v_inst_3359_, 1);
            leanh::lean_inc(v_toBind_3386_);
            v_toFunctor_3387_ = leanh::lean_ctor_get(v_toApplicative_3384_, 0);
            leanh::lean_inc_ref(v_toFunctor_3387_);
            v_toPure_3388_ = leanh::lean_ctor_get(v_toApplicative_3384_, 1);
            leanh::lean_inc(v_toPure_3388_);
            v_discrs_3389_ = leanh::lean_ctor_get(v_matcherApp_3385_, 5);
            leanh::lean_inc_ref_n(v_discrs_3389_, 2);
            v___f_3390_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0;
            v___f_3391_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed
                    as *mut core::ffi::c_void,
                5,
                1,
            );
            leanh::lean_closure_set(v___f_3391_, 0, v_onAlt_3364_);
            v___f_3392_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1;
            v___x_3393_ =
                l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9;
            v_sz_3394_ = lean_array_size(v_discrs_3389_);
            v___x_3395_ = 0usize;
            v_mask_3396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3393_,
                v___f_3392_,
                v_sz_3394_,
                v___x_3395_,
                v_discrs_3389_,
            );
            v___x_3397_ = leanh::lean_box((v_useSplitter_3365_) as usize);
            leanh::lean_inc(v_inst_3357_);
            leanh::lean_inc(v_mask_3396_);
            v___f_3398_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed
                    as *mut core::ffi::c_void,
                13,
                12,
            );
            leanh::lean_closure_set(v___f_3398_, 0, v_toFunctor_3387_);
            leanh::lean_closure_set(v___f_3398_, 1, v_mask_3396_);
            leanh::lean_closure_set(v___f_3398_, 2, v_toPure_3388_);
            leanh::lean_closure_set(v___f_3398_, 3, v_inst_3357_);
            leanh::lean_closure_set(v___f_3398_, 4, v_inst_3358_);
            leanh::lean_closure_set(v___f_3398_, 5, v_inst_3359_);
            leanh::lean_closure_set(v___f_3398_, 6, v_inst_3360_);
            leanh::lean_closure_set(v___f_3398_, 7, v_inst_3361_);
            leanh::lean_closure_set(v___f_3398_, 8, v_matcherApp_3385_);
            leanh::lean_closure_set(v___f_3398_, 9, v___x_3397_);
            leanh::lean_closure_set(v___f_3398_, 10, v___f_3391_);
            leanh::lean_closure_set(v___f_3398_, 11, v___f_3390_);
            v_maskedDiscrs_3399_ = l_Array_mask___redArg(v_mask_3396_, v_discrs_3389_);
            leanh::lean_dec(v_mask_3396_);
            v___x_3400_ = leanh::lean_alloc_closure(
                l_Lean_Expr_abstractM___boxed as *mut core::ffi::c_void,
                7,
                2,
            );
            leanh::lean_closure_set(v___x_3400_, 0, v_resTy_3363_);
            leanh::lean_closure_set(v___x_3400_, 1, v_maskedDiscrs_3399_);
            v___x_3401_ =
                leanh::lean_apply_2(v_inst_3357_, leanh::lean_box(0), v___x_3400_);
            v___x_3402_ = leanh::lean_apply_4(
                v_toBind_3386_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_3401_,
                v___f_3398_,
            );
            return v___x_3402_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(
    mut v_inst_3403_: *mut leanh::LeanObject,
    mut v_inst_3404_: *mut leanh::LeanObject,
    mut v_inst_3405_: *mut leanh::LeanObject,
    mut v_inst_3406_: *mut leanh::LeanObject,
    mut v_inst_3407_: *mut leanh::LeanObject,
    mut v_info_3408_: *mut leanh::LeanObject,
    mut v_resTy_3409_: *mut leanh::LeanObject,
    mut v_onAlt_3410_: *mut leanh::LeanObject,
    mut v_useSplitter_3411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useSplitter_boxed_3412_: u8 = 0;
    let mut v_res_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3412_ = (leanh::lean_unbox(v_useSplitter_3411_) as u8);
    v_res_3413_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(
        v_inst_3403_,
        v_inst_3404_,
        v_inst_3405_,
        v_inst_3406_,
        v_inst_3407_,
        v_info_3408_,
        v_resTy_3409_,
        v_onAlt_3410_,
        v_useSplitter_boxed_3412_,
    );
    return v_res_3413_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(
    mut v_n_3414_: *mut leanh::LeanObject,
    mut v_inst_3415_: *mut leanh::LeanObject,
    mut v_inst_3416_: *mut leanh::LeanObject,
    mut v_inst_3417_: *mut leanh::LeanObject,
    mut v_inst_3418_: *mut leanh::LeanObject,
    mut v_inst_3419_: *mut leanh::LeanObject,
    mut v_inst_3420_: *mut leanh::LeanObject,
    mut v_inst_3421_: *mut leanh::LeanObject,
    mut v_inst_3422_: *mut leanh::LeanObject,
    mut v_info_3423_: *mut leanh::LeanObject,
    mut v_resTy_3424_: *mut leanh::LeanObject,
    mut v_onAlt_3425_: *mut leanh::LeanObject,
    mut v_useSplitter_3426_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3427_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(
        v_inst_3415_,
        v_inst_3416_,
        v_inst_3417_,
        v_inst_3418_,
        v_inst_3419_,
        v_info_3423_,
        v_resTy_3424_,
        v_onAlt_3425_,
        v_useSplitter_3426_,
    );
    return v___x_3427_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(
    mut v_n_3428_: *mut leanh::LeanObject,
    mut v_inst_3429_: *mut leanh::LeanObject,
    mut v_inst_3430_: *mut leanh::LeanObject,
    mut v_inst_3431_: *mut leanh::LeanObject,
    mut v_inst_3432_: *mut leanh::LeanObject,
    mut v_inst_3433_: *mut leanh::LeanObject,
    mut v_inst_3434_: *mut leanh::LeanObject,
    mut v_inst_3435_: *mut leanh::LeanObject,
    mut v_inst_3436_: *mut leanh::LeanObject,
    mut v_info_3437_: *mut leanh::LeanObject,
    mut v_resTy_3438_: *mut leanh::LeanObject,
    mut v_onAlt_3439_: *mut leanh::LeanObject,
    mut v_useSplitter_3440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_useSplitter_boxed_3441_: u8 = 0;
    let mut v_res_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3441_ = (leanh::lean_unbox(v_useSplitter_3440_) as u8);
    v_res_3442_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(
        v_n_3428_,
        v_inst_3429_,
        v_inst_3430_,
        v_inst_3431_,
        v_inst_3432_,
        v_inst_3433_,
        v_inst_3434_,
        v_inst_3435_,
        v_inst_3436_,
        v_info_3437_,
        v_resTy_3438_,
        v_onAlt_3439_,
        v_useSplitter_boxed_3441_,
    );
    leanh::lean_dec(v_inst_3436_);
    leanh::lean_dec(v_inst_3435_);
    leanh::lean_dec_ref(v_inst_3434_);
    return v_res_3442_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(
    mut v_info_3443_: *mut leanh::LeanObject,
    mut v_e_3444_: *mut leanh::LeanObject,
    mut v_a_3445_: *mut leanh::LeanObject,
    mut v_a_3446_: *mut leanh::LeanObject,
    mut v_a_3447_: *mut leanh::LeanObject,
    mut v_a_3448_: *mut leanh::LeanObject,
    mut v_a_3449_: *mut leanh::LeanObject,
    mut v_a_3450_: *mut leanh::LeanObject,
    mut v_a_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_info_3443_) == 2 {
        let mut v_matcherApp_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toMatcherInfo_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_matcherApp_3453_ = leanh::lean_ctor_get(v_info_3443_, 0);
        leanh::lean_inc_ref(v_matcherApp_3453_);
        leanh::lean_dec_ref_known(v_info_3443_, 1);
        v_toMatcherInfo_3454_ = leanh::lean_ctor_get(v_matcherApp_3453_, 0);
        leanh::lean_inc_ref(v_toMatcherInfo_3454_);
        leanh::lean_dec_ref(v_matcherApp_3453_);
        v___x_3455_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(
            v_toMatcherInfo_3454_,
            v_e_3444_,
            v_a_3445_,
            v_a_3446_,
            v_a_3447_,
            v_a_3448_,
            v_a_3449_,
            v_a_3450_,
            v_a_3451_,
        );
        return v___x_3455_;
    } else {
        let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_3444_);
        leanh::lean_dec_ref(v_info_3443_);
        v___x_3456_ = leanh::lean_box(0);
        v___x_3457_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3457_, 0, v___x_3456_);
        return v___x_3457_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(
    mut v_info_3458_: *mut leanh::LeanObject,
    mut v_e_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
    mut v_a_3462_: *mut leanh::LeanObject,
    mut v_a_3463_: *mut leanh::LeanObject,
    mut v_a_3464_: *mut leanh::LeanObject,
    mut v_a_3465_: *mut leanh::LeanObject,
    mut v_a_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(
        v_info_3458_,
        v_e_3459_,
        v_a_3460_,
        v_a_3461_,
        v_a_3462_,
        v_a_3463_,
        v_a_3464_,
        v_a_3465_,
        v_a_3466_,
    );
    leanh::lean_dec(v_a_3466_);
    leanh::lean_dec_ref(v_a_3465_);
    leanh::lean_dec(v_a_3464_);
    leanh::lean_dec_ref(v_a_3463_);
    leanh::lean_dec(v_a_3462_);
    leanh::lean_dec_ref(v_a_3461_);
    leanh::lean_dec(v_a_3460_);
    return v_res_3468_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(
    mut v_declName_3469_: *mut leanh::LeanObject,
    mut v___y_3470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3472_ = lean_st_ref_get(v___y_3470_);
    v_env_3473_ = leanh::lean_ctor_get(v___x_3472_, 0);
    leanh::lean_inc_ref(v_env_3473_);
    leanh::lean_dec(v___x_3472_);
    v___x_3474_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3473_, v_declName_3469_);
    v___x_3475_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3475_, 0, v___x_3474_);
    return v___x_3475_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(
    mut v_declName_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
    mut v___y_3478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3479_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_3476_, v___y_3477_);
    leanh::lean_dec(v___y_3477_);
    return v_res_3479_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(
    mut v_msgData_3480_: *mut leanh::LeanObject,
    mut v___y_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
    mut v___y_3484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = lean_st_ref_get(v___y_3484_);
    v_env_3487_ = leanh::lean_ctor_get(v___x_3486_, 0);
    leanh::lean_inc_ref(v_env_3487_);
    leanh::lean_dec(v___x_3486_);
    v___x_3488_ = lean_st_ref_get(v___y_3482_);
    v_mctx_3489_ = leanh::lean_ctor_get(v___x_3488_, 0);
    leanh::lean_inc_ref(v_mctx_3489_);
    leanh::lean_dec(v___x_3488_);
    v_lctx_3490_ = leanh::lean_ctor_get(v___y_3481_, 2);
    v_options_3491_ = leanh::lean_ctor_get(v___y_3483_, 2);
    leanh::lean_inc_ref(v_options_3491_);
    leanh::lean_inc_ref(v_lctx_3490_);
    v___x_3492_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3492_, 0, v_env_3487_);
    leanh::lean_ctor_set(v___x_3492_, 1, v_mctx_3489_);
    leanh::lean_ctor_set(v___x_3492_, 2, v_lctx_3490_);
    leanh::lean_ctor_set(v___x_3492_, 3, v_options_3491_);
    v___x_3493_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3493_, 0, v___x_3492_);
    leanh::lean_ctor_set(v___x_3493_, 1, v_msgData_3480_);
    v___x_3494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3494_, 0, v___x_3493_);
    return v___x_3494_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(
    mut v_msgData_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
    mut v___y_3497_: *mut leanh::LeanObject,
    mut v___y_3498_: *mut leanh::LeanObject,
    mut v___y_3499_: *mut leanh::LeanObject,
    mut v___y_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
    leanh::lean_dec(v___y_3499_);
    leanh::lean_dec_ref(v___y_3498_);
    leanh::lean_dec(v___y_3497_);
    leanh::lean_dec_ref(v___y_3496_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(
    mut v_msg_3502_: *mut leanh::LeanObject,
    mut v___y_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
    mut v___y_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3508_ = leanh::lean_ctor_get(v___y_3505_, 5);
                v___x_3509_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
                v_a_3510_ = leanh::lean_ctor_get(v___x_3509_, 0);
                v_isSharedCheck_3518_ = (!leanh::lean_is_exclusive(v___x_3509_)) as u8;
                if v_isSharedCheck_3518_ == 0 {
                    v___x_3512_ = v___x_3509_;
                    v_isShared_3513_ = v_isSharedCheck_3518_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3510_);
                    leanh::lean_dec(v___x_3509_);
                    v___x_3512_ = leanh::lean_box(0);
                    v_isShared_3513_ = v_isSharedCheck_3518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3508_);
                v___x_3514_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3514_, 0, v_ref_3508_);
                leanh::lean_ctor_set(v___x_3514_, 1, v_a_3510_);
                if v_isShared_3513_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3512_, 1);
                    leanh::lean_ctor_set(v___x_3512_, 0, v___x_3514_);
                    v___x_3516_ = v___x_3512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
                    v___x_3516_ = v_reuseFailAlloc_3517_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(
    mut v_msg_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
    mut v___y_3521_: *mut leanh::LeanObject,
    mut v___y_3522_: *mut leanh::LeanObject,
    mut v___y_3523_: *mut leanh::LeanObject,
    mut v___y_3524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3525_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
    leanh::lean_dec(v___y_3523_);
    leanh::lean_dec_ref(v___y_3522_);
    leanh::lean_dec(v___y_3521_);
    leanh::lean_dec_ref(v___y_3520_);
    return v_res_3525_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(
    mut v_ref_3526_: *mut leanh::LeanObject,
    mut v_msg_3527_: *mut leanh::LeanObject,
    mut v___y_3528_: *mut leanh::LeanObject,
    mut v___y_3529_: *mut leanh::LeanObject,
    mut v___y_3530_: *mut leanh::LeanObject,
    mut v___y_3531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3545_: u8 = 0;
    let mut v_cancelTk_x3f_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3547_: u8 = 0;
    let mut v_inheritedTraceOptions_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3533_ = leanh::lean_ctor_get(v___y_3530_, 0);
    v_fileMap_3534_ = leanh::lean_ctor_get(v___y_3530_, 1);
    v_options_3535_ = leanh::lean_ctor_get(v___y_3530_, 2);
    v_currRecDepth_3536_ = leanh::lean_ctor_get(v___y_3530_, 3);
    v_maxRecDepth_3537_ = leanh::lean_ctor_get(v___y_3530_, 4);
    v_ref_3538_ = leanh::lean_ctor_get(v___y_3530_, 5);
    v_currNamespace_3539_ = leanh::lean_ctor_get(v___y_3530_, 6);
    v_openDecls_3540_ = leanh::lean_ctor_get(v___y_3530_, 7);
    v_initHeartbeats_3541_ = leanh::lean_ctor_get(v___y_3530_, 8);
    v_maxHeartbeats_3542_ = leanh::lean_ctor_get(v___y_3530_, 9);
    v_quotContext_3543_ = leanh::lean_ctor_get(v___y_3530_, 10);
    v_currMacroScope_3544_ = leanh::lean_ctor_get(v___y_3530_, 11);
    v_diag_3545_ = leanh::lean_ctor_get_uint8(
        v___y_3530_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3546_ = leanh::lean_ctor_get(v___y_3530_, 12);
    v_suppressElabErrors_3547_ = leanh::lean_ctor_get_uint8(
        v___y_3530_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3548_ = leanh::lean_ctor_get(v___y_3530_, 13);
    v_ref_3549_ = l_Lean_replaceRef(v_ref_3526_, v_ref_3538_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3548_);
    leanh::lean_inc(v_cancelTk_x3f_3546_);
    leanh::lean_inc(v_currMacroScope_3544_);
    leanh::lean_inc(v_quotContext_3543_);
    leanh::lean_inc(v_maxHeartbeats_3542_);
    leanh::lean_inc(v_initHeartbeats_3541_);
    leanh::lean_inc(v_openDecls_3540_);
    leanh::lean_inc(v_currNamespace_3539_);
    leanh::lean_inc(v_maxRecDepth_3537_);
    leanh::lean_inc(v_currRecDepth_3536_);
    leanh::lean_inc_ref(v_options_3535_);
    leanh::lean_inc_ref(v_fileMap_3534_);
    leanh::lean_inc_ref(v_fileName_3533_);
    v___x_3550_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3550_, 0, v_fileName_3533_);
    leanh::lean_ctor_set(v___x_3550_, 1, v_fileMap_3534_);
    leanh::lean_ctor_set(v___x_3550_, 2, v_options_3535_);
    leanh::lean_ctor_set(v___x_3550_, 3, v_currRecDepth_3536_);
    leanh::lean_ctor_set(v___x_3550_, 4, v_maxRecDepth_3537_);
    leanh::lean_ctor_set(v___x_3550_, 5, v_ref_3549_);
    leanh::lean_ctor_set(v___x_3550_, 6, v_currNamespace_3539_);
    leanh::lean_ctor_set(v___x_3550_, 7, v_openDecls_3540_);
    leanh::lean_ctor_set(v___x_3550_, 8, v_initHeartbeats_3541_);
    leanh::lean_ctor_set(v___x_3550_, 9, v_maxHeartbeats_3542_);
    leanh::lean_ctor_set(v___x_3550_, 10, v_quotContext_3543_);
    leanh::lean_ctor_set(v___x_3550_, 11, v_currMacroScope_3544_);
    leanh::lean_ctor_set(v___x_3550_, 12, v_cancelTk_x3f_3546_);
    leanh::lean_ctor_set(v___x_3550_, 13, v_inheritedTraceOptions_3548_);
    leanh::lean_ctor_set_uint8(
        v___x_3550_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3545_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3550_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3547_,
    );
    v___x_3551_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_3527_, v___y_3528_, v___y_3529_, v___x_3550_, v___y_3531_);
    leanh::lean_dec_ref_known(v___x_3550_, 14);
    return v___x_3551_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_ref_3552_: *mut leanh::LeanObject,
    mut v_msg_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_3552_, v_msg_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
    leanh::lean_dec(v___y_3557_);
    leanh::lean_dec_ref(v___y_3556_);
    leanh::lean_dec(v___y_3555_);
    leanh::lean_dec_ref(v___y_3554_);
    leanh::lean_dec(v_ref_3552_);
    return v_res_3559_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3560_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3560_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3561_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
    v___x_3562_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3562_, 0, v___x_3561_);
    return v___x_3562_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3563_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_3564_ = leanh::lean_unsigned_to_nat(0);
    v___x_3565_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3565_, 0, v___x_3564_);
    leanh::lean_ctor_set(v___x_3565_, 1, v___x_3564_);
    leanh::lean_ctor_set(v___x_3565_, 2, v___x_3564_);
    leanh::lean_ctor_set(v___x_3565_, 3, v___x_3564_);
    leanh::lean_ctor_set(v___x_3565_, 4, v___x_3563_);
    leanh::lean_ctor_set(v___x_3565_, 5, v___x_3563_);
    leanh::lean_ctor_set(v___x_3565_, 6, v___x_3563_);
    leanh::lean_ctor_set(v___x_3565_, 7, v___x_3563_);
    leanh::lean_ctor_set(v___x_3565_, 8, v___x_3563_);
    leanh::lean_ctor_set(v___x_3565_, 9, v___x_3563_);
    return v___x_3565_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3566_ = leanh::lean_unsigned_to_nat(32);
    v___x_3567_ = lean_mk_empty_array_with_capacity(v___x_3566_);
    v___x_3568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3567_);
    return v___x_3568_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3569_: usize = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3569_ = 5usize;
    v___x_3570_ = leanh::lean_unsigned_to_nat(0);
    v___x_3571_ = leanh::lean_unsigned_to_nat(32);
    v___x_3572_ = lean_mk_empty_array_with_capacity(v___x_3571_);
    v___x_3573_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
    v___x_3574_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3574_, 0, v___x_3573_);
    leanh::lean_ctor_set(v___x_3574_, 1, v___x_3572_);
    leanh::lean_ctor_set(v___x_3574_, 2, v___x_3570_);
    leanh::lean_ctor_set(v___x_3574_, 3, v___x_3570_);
    leanh::lean_ctor_set_usize(v___x_3574_, 4, v___x_3569_);
    return v___x_3574_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3575_ = leanh::lean_box(1);
    v___x_3576_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
    v___x_3577_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_3578_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3578_, 0, v___x_3577_);
    leanh::lean_ctor_set(v___x_3578_, 1, v___x_3576_);
    leanh::lean_ctor_set(v___x_3578_, 2, v___x_3575_);
    return v___x_3578_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3580_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6;
    v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
    return v___x_3581_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3583_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8;
    v___x_3584_ = l_Lean_stringToMessageData(v___x_3583_);
    return v___x_3584_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10;
    v___x_3587_ = l_Lean_stringToMessageData(v___x_3586_);
    return v___x_3587_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3589_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12;
    v___x_3590_ = l_Lean_stringToMessageData(v___x_3589_);
    return v___x_3590_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14;
    v___x_3593_ = l_Lean_stringToMessageData(v___x_3592_);
    return v___x_3593_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16;
    v___x_3596_ = l_Lean_stringToMessageData(v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18;
    v___x_3599_ = l_Lean_stringToMessageData(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(
    mut v_msg_3600_: *mut leanh::LeanObject,
    mut v_declHint_3601_: *mut leanh::LeanObject,
    mut v___y_3602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: u8 = 0;
    let mut v_isExporting_3607_: u8 = 0;
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3604_ = lean_st_ref_get(v___y_3602_);
                v_env_3605_ = leanh::lean_ctor_get(v___x_3604_, 0);
                leanh::lean_inc_ref(v_env_3605_);
                leanh::lean_dec(v___x_3604_);
                v___x_3606_ = l_Lean_Name_isAnonymous(v_declHint_3601_);
                if v___x_3606_ == 0 {
                    v_isExporting_3607_ = leanh::lean_ctor_get_uint8(
                        v_env_3605_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3607_ == 0 {
                        leanh::lean_dec_ref(v_env_3605_);
                        leanh::lean_dec(v_declHint_3601_);
                        v___x_3608_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3608_, 0, v_msg_3600_);
                        return v___x_3608_;
                    } else {
                        leanh::lean_inc_ref(v_env_3605_);
                        v___x_3609_ = l_Lean_Environment_setExporting(v_env_3605_, v___x_3606_);
                        leanh::lean_inc(v_declHint_3601_);
                        leanh::lean_inc_ref(v___x_3609_);
                        v___x_3610_ = l_Lean_Environment_contains(
                            v___x_3609_,
                            v_declHint_3601_,
                            v_isExporting_3607_,
                        );
                        if v___x_3610_ == 0 {
                            leanh::lean_dec_ref(v___x_3609_);
                            leanh::lean_dec_ref(v_env_3605_);
                            leanh::lean_dec(v_declHint_3601_);
                            v___x_3611_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3611_, 0, v_msg_3600_);
                            return v___x_3611_;
                        } else {
                            v___x_3612_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
                            v___x_3613_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
                            v___x_3614_ = l_Lean_Options_empty;
                            v___x_3615_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3615_, 0, v___x_3609_);
                            leanh::lean_ctor_set(v___x_3615_, 1, v___x_3612_);
                            leanh::lean_ctor_set(v___x_3615_, 2, v___x_3613_);
                            leanh::lean_ctor_set(v___x_3615_, 3, v___x_3614_);
                            leanh::lean_inc(v_declHint_3601_);
                            v___x_3616_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3601_, v___x_3606_);
                            v_c_3617_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3617_, 0, v___x_3615_);
                            leanh::lean_ctor_set(v_c_3617_, 1, v___x_3616_);
                            v___x_3618_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3605_,
                                v_declHint_3601_,
                            );
                            if leanh::lean_obj_tag(v___x_3618_) == 0 {
                                leanh::lean_dec_ref(v_env_3605_);
                                leanh::lean_dec(v_declHint_3601_);
                                v___x_3619_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
                                v___x_3620_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3620_, 0, v___x_3619_);
                                leanh::lean_ctor_set(v___x_3620_, 1, v_c_3617_);
                                v___x_3621_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
                                v___x_3622_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3622_, 0, v___x_3620_);
                                leanh::lean_ctor_set(v___x_3622_, 1, v___x_3621_);
                                v___x_3623_ = l_Lean_MessageData_note(v___x_3622_);
                                v___x_3624_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3624_, 0, v_msg_3600_);
                                leanh::lean_ctor_set(v___x_3624_, 1, v___x_3623_);
                                v___x_3625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3625_, 0, v___x_3624_);
                                return v___x_3625_;
                            } else {
                                v_val_3626_ = leanh::lean_ctor_get(v___x_3618_, 0);
                                v_isSharedCheck_3661_ =
                                    (!leanh::lean_is_exclusive(v___x_3618_)) as u8;
                                if v_isSharedCheck_3661_ == 0 {
                                    v___x_3628_ = v___x_3618_;
                                    v_isShared_3629_ = v_isSharedCheck_3661_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3626_);
                                    leanh::lean_dec(v___x_3618_);
                                    v___x_3628_ = leanh::lean_box(0);
                                    v_isShared_3629_ = v_isSharedCheck_3661_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3605_);
                    leanh::lean_dec(v_declHint_3601_);
                    v___x_3662_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3662_, 0, v_msg_3600_);
                    return v___x_3662_;
                }
            }
            1 => {
                v___x_3630_ = leanh::lean_box(0);
                v___x_3631_ = l_Lean_Environment_header(v_env_3605_);
                leanh::lean_dec_ref(v_env_3605_);
                v___x_3632_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3631_);
                v_mod_3633_ = lean_array_get(v___x_3630_, v___x_3632_, v_val_3626_);
                leanh::lean_dec(v_val_3626_);
                leanh::lean_dec_ref(v___x_3632_);
                v___x_3634_ = l_Lean_isPrivateName(v_declHint_3601_);
                leanh::lean_dec(v_declHint_3601_);
                if v___x_3634_ == 0 {
                    v___x_3635_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
                    v___x_3636_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3636_, 0, v___x_3635_);
                    leanh::lean_ctor_set(v___x_3636_, 1, v_c_3617_);
                    v___x_3637_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
                    v___x_3638_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3638_, 0, v___x_3636_);
                    leanh::lean_ctor_set(v___x_3638_, 1, v___x_3637_);
                    v___x_3639_ = l_Lean_MessageData_ofName(v_mod_3633_);
                    v___x_3640_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3640_, 0, v___x_3638_);
                    leanh::lean_ctor_set(v___x_3640_, 1, v___x_3639_);
                    v___x_3641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
                    v___x_3642_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3642_, 0, v___x_3640_);
                    leanh::lean_ctor_set(v___x_3642_, 1, v___x_3641_);
                    v___x_3643_ = l_Lean_MessageData_note(v___x_3642_);
                    v___x_3644_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3644_, 0, v_msg_3600_);
                    leanh::lean_ctor_set(v___x_3644_, 1, v___x_3643_);
                    if v_isShared_3629_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3628_, 0);
                        leanh::lean_ctor_set(v___x_3628_, 0, v___x_3644_);
                        v___x_3646_ = v___x_3628_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
                        v___x_3646_ = v_reuseFailAlloc_3647_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3648_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
                    v___x_3649_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3649_, 0, v___x_3648_);
                    leanh::lean_ctor_set(v___x_3649_, 1, v_c_3617_);
                    v___x_3650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
                    v___x_3651_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3651_, 0, v___x_3649_);
                    leanh::lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                    v___x_3652_ = l_Lean_MessageData_ofName(v_mod_3633_);
                    v___x_3653_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3653_, 0, v___x_3651_);
                    leanh::lean_ctor_set(v___x_3653_, 1, v___x_3652_);
                    v___x_3654_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
                    v___x_3655_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3655_, 0, v___x_3653_);
                    leanh::lean_ctor_set(v___x_3655_, 1, v___x_3654_);
                    v___x_3656_ = l_Lean_MessageData_note(v___x_3655_);
                    v___x_3657_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3657_, 0, v_msg_3600_);
                    leanh::lean_ctor_set(v___x_3657_, 1, v___x_3656_);
                    if v_isShared_3629_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3628_, 0);
                        leanh::lean_ctor_set(v___x_3628_, 0, v___x_3657_);
                        v___x_3659_ = v___x_3628_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
                        v___x_3659_ = v_reuseFailAlloc_3660_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3646_;
            }
            3 => {
                return v___x_3659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(
    mut v_msg_3663_: *mut leanh::LeanObject,
    mut v_declHint_3664_: *mut leanh::LeanObject,
    mut v___y_3665_: *mut leanh::LeanObject,
    mut v___y_3666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_3663_, v_declHint_3664_, v___y_3665_);
    leanh::lean_dec(v___y_3665_);
    return v_res_3667_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(
    mut v_msg_3668_: *mut leanh::LeanObject,
    mut v_declHint_3669_: *mut leanh::LeanObject,
    mut v___y_3670_: *mut leanh::LeanObject,
    mut v___y_3671_: *mut leanh::LeanObject,
    mut v___y_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3679_: u8 = 0;
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3675_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_3668_, v_declHint_3669_, v___y_3673_);
                v_a_3676_ = leanh::lean_ctor_get(v___x_3675_, 0);
                v_isSharedCheck_3685_ = (!leanh::lean_is_exclusive(v___x_3675_)) as u8;
                if v_isSharedCheck_3685_ == 0 {
                    v___x_3678_ = v___x_3675_;
                    v_isShared_3679_ = v_isSharedCheck_3685_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3676_);
                    leanh::lean_dec(v___x_3675_);
                    v___x_3678_ = leanh::lean_box(0);
                    v_isShared_3679_ = v_isSharedCheck_3685_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3680_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3681_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3681_, 0, v___x_3680_);
                leanh::lean_ctor_set(v___x_3681_, 1, v_a_3676_);
                if v_isShared_3679_ == 0 {
                    leanh::lean_ctor_set(v___x_3678_, 0, v___x_3681_);
                    v___x_3683_ = v___x_3678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
                    v___x_3683_ = v_reuseFailAlloc_3684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(
    mut v_msg_3686_: *mut leanh::LeanObject,
    mut v_declHint_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_3686_, v_declHint_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
    leanh::lean_dec(v___y_3691_);
    leanh::lean_dec_ref(v___y_3690_);
    leanh::lean_dec(v___y_3689_);
    leanh::lean_dec_ref(v___y_3688_);
    return v_res_3693_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_3694_: *mut leanh::LeanObject,
    mut v_msg_3695_: *mut leanh::LeanObject,
    mut v_declHint_3696_: *mut leanh::LeanObject,
    mut v___y_3697_: *mut leanh::LeanObject,
    mut v___y_3698_: *mut leanh::LeanObject,
    mut v___y_3699_: *mut leanh::LeanObject,
    mut v___y_3700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3702_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_3695_, v_declHint_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
    v_a_3703_ = leanh::lean_ctor_get(v___x_3702_, 0);
    leanh::lean_inc(v_a_3703_);
    leanh::lean_dec_ref(v___x_3702_);
    v___x_3704_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_3694_, v_a_3703_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
    return v___x_3704_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_3705_: *mut leanh::LeanObject,
    mut v_msg_3706_: *mut leanh::LeanObject,
    mut v_declHint_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
    mut v___y_3710_: *mut leanh::LeanObject,
    mut v___y_3711_: *mut leanh::LeanObject,
    mut v___y_3712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3713_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3705_, v_msg_3706_, v_declHint_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
    leanh::lean_dec(v___y_3711_);
    leanh::lean_dec_ref(v___y_3710_);
    leanh::lean_dec(v___y_3709_);
    leanh::lean_dec_ref(v___y_3708_);
    leanh::lean_dec(v_ref_3705_);
    return v_res_3713_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3715_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0;
    v___x_3716_ = l_Lean_stringToMessageData(v___x_3715_);
    return v___x_3716_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3718_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2;
    v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
    return v___x_3719_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_3720_: *mut leanh::LeanObject,
    mut v_constName_3721_: *mut leanh::LeanObject,
    mut v___y_3722_: *mut leanh::LeanObject,
    mut v___y_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
    mut v___y_3725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: u8 = 0;
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3727_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
    v___x_3728_ = 0;
    leanh::lean_inc(v_constName_3721_);
    v___x_3729_ = l_Lean_MessageData_ofConstName(v_constName_3721_, v___x_3728_);
    v___x_3730_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3730_, 0, v___x_3727_);
    leanh::lean_ctor_set(v___x_3730_, 1, v___x_3729_);
    v___x_3731_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
    v___x_3732_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3732_, 0, v___x_3730_);
    leanh::lean_ctor_set(v___x_3732_, 1, v___x_3731_);
    v___x_3733_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3720_, v___x_3732_, v_constName_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
    return v___x_3733_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_3734_: *mut leanh::LeanObject,
    mut v_constName_3735_: *mut leanh::LeanObject,
    mut v___y_3736_: *mut leanh::LeanObject,
    mut v___y_3737_: *mut leanh::LeanObject,
    mut v___y_3738_: *mut leanh::LeanObject,
    mut v___y_3739_: *mut leanh::LeanObject,
    mut v___y_3740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3734_, v_constName_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
    leanh::lean_dec(v___y_3739_);
    leanh::lean_dec_ref(v___y_3738_);
    leanh::lean_dec(v___y_3737_);
    leanh::lean_dec_ref(v___y_3736_);
    leanh::lean_dec(v_ref_3734_);
    return v_res_3741_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_constName_3742_: *mut leanh::LeanObject,
    mut v___y_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3748_ = leanh::lean_ctor_get(v___y_3745_, 5);
    v___x_3749_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3748_, v_constName_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
    return v___x_3749_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_3750_: *mut leanh::LeanObject,
    mut v___y_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
    mut v___y_3754_: *mut leanh::LeanObject,
    mut v___y_3755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3756_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
    leanh::lean_dec(v___y_3754_);
    leanh::lean_dec_ref(v___y_3753_);
    leanh::lean_dec(v___y_3752_);
    leanh::lean_dec_ref(v___y_3751_);
    return v_res_3756_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(
    mut v_constName_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: u8 = 0;
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3763_ = lean_st_ref_get(v___y_3761_);
                v_env_3764_ = leanh::lean_ctor_get(v___x_3763_, 0);
                leanh::lean_inc_ref(v_env_3764_);
                leanh::lean_dec(v___x_3763_);
                v___x_3765_ = 0;
                leanh::lean_inc(v_constName_3757_);
                v___x_3766_ =
                    l_Lean_Environment_find_x3f(v_env_3764_, v_constName_3757_, v___x_3765_);
                if leanh::lean_obj_tag(v___x_3766_) == 0 {
                    v___x_3767_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
                    return v___x_3767_;
                } else {
                    leanh::lean_dec(v_constName_3757_);
                    v_val_3768_ = leanh::lean_ctor_get(v___x_3766_, 0);
                    v_isSharedCheck_3775_ = (!leanh::lean_is_exclusive(v___x_3766_)) as u8;
                    if v_isSharedCheck_3775_ == 0 {
                        v___x_3770_ = v___x_3766_;
                        v_isShared_3771_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3768_);
                        leanh::lean_dec(v___x_3766_);
                        v___x_3770_ = leanh::lean_box(0);
                        v_isShared_3771_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3771_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3770_, 0);
                    v___x_3773_ = v___x_3770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_val_3768_);
                    v___x_3773_ = v_reuseFailAlloc_3774_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(
    mut v_constName_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
    mut v___y_3781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
    leanh::lean_dec(v___y_3780_);
    leanh::lean_dec_ref(v___y_3779_);
    leanh::lean_dec(v___y_3778_);
    leanh::lean_dec_ref(v___y_3777_);
    return v_res_3782_;
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(
    mut v_msg_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___y_3785_: *mut leanh::LeanObject,
    mut v___y_3786_: *mut leanh::LeanObject,
    mut v___y_3787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3809_: u8 = 0;
    let mut v_toFunctor_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3816_: u8 = 0;
    let mut v___f_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921__overap_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v_unused_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_unused_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3789_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1,
                );
                v_toApplicative_3790_ = leanh::lean_ctor_get(v___x_3789_, 0);
                v_toFunctor_3791_ = leanh::lean_ctor_get(v_toApplicative_3790_, 0);
                v_toSeq_3792_ = leanh::lean_ctor_get(v_toApplicative_3790_, 2);
                v_toSeqLeft_3793_ = leanh::lean_ctor_get(v_toApplicative_3790_, 3);
                v_toSeqRight_3794_ = leanh::lean_ctor_get(v_toApplicative_3790_, 4);
                v___f_3795_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2;
                v___f_3796_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3;
                leanh::lean_inc_ref_n(v_toFunctor_3791_, 2);
                v___f_3797_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3797_, 0, v_toFunctor_3791_);
                v___f_3798_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3798_, 0, v_toFunctor_3791_);
                v___x_3799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3799_, 0, v___f_3797_);
                leanh::lean_ctor_set(v___x_3799_, 1, v___f_3798_);
                leanh::lean_inc(v_toSeqRight_3794_);
                v___f_3800_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3800_, 0, v_toSeqRight_3794_);
                leanh::lean_inc(v_toSeqLeft_3793_);
                v___f_3801_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3801_, 0, v_toSeqLeft_3793_);
                leanh::lean_inc(v_toSeq_3792_);
                v___f_3802_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3802_, 0, v_toSeq_3792_);
                v___x_3803_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3803_, 0, v___x_3799_);
                leanh::lean_ctor_set(v___x_3803_, 1, v___f_3795_);
                leanh::lean_ctor_set(v___x_3803_, 2, v___f_3802_);
                leanh::lean_ctor_set(v___x_3803_, 3, v___f_3801_);
                leanh::lean_ctor_set(v___x_3803_, 4, v___f_3800_);
                v___x_3804_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3804_, 0, v___x_3803_);
                leanh::lean_ctor_set(v___x_3804_, 1, v___f_3796_);
                v___x_3805_ = l_StateRefT_x27_instMonad___redArg(v___x_3804_);
                v_toApplicative_3806_ = leanh::lean_ctor_get(v___x_3805_, 0);
                v_isSharedCheck_3837_ = (!leanh::lean_is_exclusive(v___x_3805_)) as u8;
                if v_isSharedCheck_3837_ == 0 {
                    v_unused_3838_ = leanh::lean_ctor_get(v___x_3805_, 1);
                    leanh::lean_dec(v_unused_3838_);
                    v___x_3808_ = v___x_3805_;
                    v_isShared_3809_ = v_isSharedCheck_3837_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_3806_);
                    leanh::lean_dec(v___x_3805_);
                    v___x_3808_ = leanh::lean_box(0);
                    v_isShared_3809_ = v_isSharedCheck_3837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3810_ = leanh::lean_ctor_get(v_toApplicative_3806_, 0);
                v_toSeq_3811_ = leanh::lean_ctor_get(v_toApplicative_3806_, 2);
                v_toSeqLeft_3812_ = leanh::lean_ctor_get(v_toApplicative_3806_, 3);
                v_toSeqRight_3813_ = leanh::lean_ctor_get(v_toApplicative_3806_, 4);
                v_isSharedCheck_3835_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_3806_)) as u8;
                if v_isSharedCheck_3835_ == 0 {
                    v_unused_3836_ = leanh::lean_ctor_get(v_toApplicative_3806_, 1);
                    leanh::lean_dec(v_unused_3836_);
                    v___x_3815_ = v_toApplicative_3806_;
                    v_isShared_3816_ = v_isSharedCheck_3835_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_3813_);
                    leanh::lean_inc(v_toSeqLeft_3812_);
                    leanh::lean_inc(v_toSeq_3811_);
                    leanh::lean_inc(v_toFunctor_3810_);
                    leanh::lean_dec(v_toApplicative_3806_);
                    v___x_3815_ = leanh::lean_box(0);
                    v_isShared_3816_ = v_isSharedCheck_3835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3817_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4;
                v___f_3818_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5;
                leanh::lean_inc_ref(v_toFunctor_3810_);
                v___f_3819_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3819_, 0, v_toFunctor_3810_);
                v___f_3820_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3820_, 0, v_toFunctor_3810_);
                v___x_3821_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3821_, 0, v___f_3819_);
                leanh::lean_ctor_set(v___x_3821_, 1, v___f_3820_);
                v___f_3822_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3822_, 0, v_toSeqRight_3813_);
                v___f_3823_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3823_, 0, v_toSeqLeft_3812_);
                v___f_3824_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_3824_, 0, v_toSeq_3811_);
                if v_isShared_3816_ == 0 {
                    leanh::lean_ctor_set(v___x_3815_, 4, v___f_3822_);
                    leanh::lean_ctor_set(v___x_3815_, 3, v___f_3823_);
                    leanh::lean_ctor_set(v___x_3815_, 2, v___f_3824_);
                    leanh::lean_ctor_set(v___x_3815_, 1, v___f_3817_);
                    leanh::lean_ctor_set(v___x_3815_, 0, v___x_3821_);
                    v___x_3826_ = v___x_3815_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___f_3817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 2, v___f_3824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 3, v___f_3823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 4, v___f_3822_);
                    v___x_3826_ = v_reuseFailAlloc_3834_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3809_ == 0 {
                    leanh::lean_ctor_set(v___x_3808_, 1, v___f_3818_);
                    leanh::lean_ctor_set(v___x_3808_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3808_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 1, v___f_3818_);
                    v___x_3828_ = v_reuseFailAlloc_3833_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3829_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
                v___x_3830_ = l_instInhabitedOfMonad___redArg(v___x_3828_, v___x_3829_);
                v___x_2921__overap_3831_ = lean_panic_fn_borrowed(v___x_3830_, v_msg_3783_);
                leanh::lean_dec(v___x_3830_);
                leanh::lean_inc(v___y_3787_);
                leanh::lean_inc_ref(v___y_3786_);
                leanh::lean_inc(v___y_3785_);
                leanh::lean_inc_ref(v___y_3784_);
                v___x_3832_ = leanh::lean_apply_5(
                    v___x_2921__overap_3831_,
                    v___y_3784_,
                    v___y_3785_,
                    v___y_3786_,
                    v___y_3787_,
                    leanh::lean_box(0),
                );
                return v___x_3832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(
    mut v_msg_3839_: *mut leanh::LeanObject,
    mut v___y_3840_: *mut leanh::LeanObject,
    mut v___y_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
    mut v___y_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3845_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
    leanh::lean_dec(v___y_3843_);
    leanh::lean_dec_ref(v___y_3842_);
    leanh::lean_dec(v___y_3841_);
    leanh::lean_dec_ref(v___y_3840_);
    return v_res_3845_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2;
    v___x_3850_ = leanh::lean_unsigned_to_nat(53);
    v___x_3851_ = leanh::lean_unsigned_to_nat(62);
    v___x_3852_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1;
    v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0;
    v___x_3854_ = l_mkPanicMessageWithDecl(
        v___x_3853_,
        v___x_3852_,
        v___x_3851_,
        v___x_3850_,
        v___x_3849_,
    );
    return v___x_3854_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(
    mut v_sz_3855_: usize,
    mut v_i_3856_: usize,
    mut v_bs_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: usize = 0;
    let mut v___x_3873_: usize = 0;
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v_a_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3863_ = lean_usize_dec_lt(v_i_3856_, v_sz_3855_);
                if v___x_3863_ == 0 {
                    v___x_3864_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3864_, 0, v_bs_3857_);
                    return v___x_3864_;
                } else {
                    v_v_3865_ = lean_array_uget_borrowed(v_bs_3857_, v_i_3856_);
                    leanh::lean_inc(v_v_3865_);
                    v___x_3866_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_3865_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
                    if leanh::lean_obj_tag(v___x_3866_) == 0 {
                        v_a_3867_ = leanh::lean_ctor_get(v___x_3866_, 0);
                        leanh::lean_inc(v_a_3867_);
                        leanh::lean_dec_ref_known(v___x_3866_, 1);
                        v___x_3868_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3869_ = lean_array_uset(v_bs_3857_, v_i_3856_, v___x_3868_);
                        if leanh::lean_obj_tag(v_a_3867_) == 6 {
                            v_val_3876_ = leanh::lean_ctor_get(v_a_3867_, 0);
                            leanh::lean_inc_ref(v_val_3876_);
                            leanh::lean_dec_ref_known(v_a_3867_, 1);
                            v_numFields_3877_ = leanh::lean_ctor_get(v_val_3876_, 4);
                            leanh::lean_inc(v_numFields_3877_);
                            leanh::lean_dec_ref(v_val_3876_);
                            v___x_3878_ = 0;
                            v___x_3879_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            leanh::lean_ctor_set(v___x_3879_, 0, v_numFields_3877_);
                            leanh::lean_ctor_set(v___x_3879_, 1, v___x_3868_);
                            leanh::lean_ctor_set_uint8(
                                v___x_3879_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v___x_3878_,
                            );
                            v_a_3871_ = v___x_3879_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3867_);
                            v___x_3880_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
                            v___x_3881_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_3880_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
                            if leanh::lean_obj_tag(v___x_3881_) == 0 {
                                v_a_3882_ = leanh::lean_ctor_get(v___x_3881_, 0);
                                leanh::lean_inc(v_a_3882_);
                                leanh::lean_dec_ref_known(v___x_3881_, 1);
                                v_a_3871_ = v_a_3882_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_bs_x27_3869_);
                                v_a_3883_ = leanh::lean_ctor_get(v___x_3881_, 0);
                                v_isSharedCheck_3890_ =
                                    (!leanh::lean_is_exclusive(v___x_3881_)) as u8;
                                if v_isSharedCheck_3890_ == 0 {
                                    v___x_3885_ = v___x_3881_;
                                    v_isShared_3886_ = v_isSharedCheck_3890_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3883_);
                                    leanh::lean_dec(v___x_3881_);
                                    v___x_3885_ = leanh::lean_box(0);
                                    v_isShared_3886_ = v_isSharedCheck_3890_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_bs_3857_);
                        v_a_3891_ = leanh::lean_ctor_get(v___x_3866_, 0);
                        v_isSharedCheck_3898_ =
                            (!leanh::lean_is_exclusive(v___x_3866_)) as u8;
                        if v_isSharedCheck_3898_ == 0 {
                            v___x_3893_ = v___x_3866_;
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3891_);
                            leanh::lean_dec(v___x_3866_);
                            v___x_3893_ = leanh::lean_box(0);
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3872_ = 1usize;
                v___x_3873_ = lean_usize_add(v_i_3856_, v___x_3872_);
                v___x_3874_ = lean_array_uset(v_bs_x27_3869_, v_i_3856_, v_a_3871_);
                v_i_3856_ = v___x_3873_;
                v_bs_3857_ = v___x_3874_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3886_ == 0 {
                    v___x_3888_ = v___x_3885_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3889_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
                    v___x_3888_ = v_reuseFailAlloc_3889_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3888_;
            }
            4 => {
                if v_isShared_3894_ == 0 {
                    v___x_3896_ = v___x_3893_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
                    v___x_3896_ = v_reuseFailAlloc_3897_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(
    mut v_sz_3899_: *mut leanh::LeanObject,
    mut v_i_3900_: *mut leanh::LeanObject,
    mut v_bs_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
    mut v___y_3906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3907_: usize = 0;
    let mut v_i_boxed_3908_: usize = 0;
    let mut v_res_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3907_ = leanh::lean_unbox_usize(v_sz_3899_);
    leanh::lean_dec(v_sz_3899_);
    v_i_boxed_3908_ = leanh::lean_unbox_usize(v_i_3900_);
    leanh::lean_dec(v_i_3900_);
    v_res_3909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_3907_, v_i_boxed_3908_, v_bs_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
    leanh::lean_dec(v___y_3905_);
    leanh::lean_dec_ref(v___y_3904_);
    leanh::lean_dec(v___y_3903_);
    leanh::lean_dec_ref(v___y_3902_);
    return v_res_3909_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3910_ = leanh::lean_box(0);
    v_dummy_3911_ = l_Lean_Expr_sort___override(v___x_3910_);
    return v_dummy_3911_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = leanh::lean_box(0);
    v___x_3913_ = leanh::lean_unsigned_to_nat(16);
    v___x_3914_ = lean_mk_array(v___x_3913_, v___x_3912_);
    return v___x_3914_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3915_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
    v___x_3916_ = leanh::lean_unsigned_to_nat(0);
    v___x_3917_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3917_, 0, v___x_3916_);
    leanh::lean_ctor_set(v___x_3917_, 1, v___x_3915_);
    return v___x_3917_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(
    mut v_e_3920_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_3921_: u8,
    mut v___y_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v_val_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v_dummy_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v_numParams_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3983_: u8 = 0;
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v_indName_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3992_: u8 = 0;
    let mut v_val_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v_toConstantVal_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4031_: usize = 0;
    let mut v___x_4032_: usize = 0;
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v_start_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v_a_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_lower_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u8 = 0;
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_a_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut v_isSharedCheck_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3930_ = l_Lean_Expr_isApp(v_e_3920_);
                if v___x_3930_ == 0 {
                    leanh::lean_dec_ref(v_e_3920_);
                    v___x_3931_ = leanh::lean_box(0);
                    v___x_3932_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3932_, 0, v___x_3931_);
                    return v___x_3932_;
                } else {
                    v___x_3933_ = l_Lean_Expr_getAppFn(v_e_3920_);
                    if leanh::lean_obj_tag(v___x_3933_) == 4 {
                        v_declName_3934_ = leanh::lean_ctor_get(v___x_3933_, 0);
                        leanh::lean_inc_n(v_declName_3934_, 2);
                        v_us_3935_ = leanh::lean_ctor_get(v___x_3933_, 1);
                        leanh::lean_inc(v_us_3935_);
                        leanh::lean_dec_ref_known(v___x_3933_, 2);
                        v___x_3936_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_3934_, v___y_3925_);
                        v_a_3937_ = leanh::lean_ctor_get(v___x_3936_, 0);
                        v_isSharedCheck_4091_ =
                            (!leanh::lean_is_exclusive(v___x_3936_)) as u8;
                        if v_isSharedCheck_4091_ == 0 {
                            v___x_3939_ = v___x_3936_;
                            v_isShared_3940_ = v_isSharedCheck_4091_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3937_);
                            leanh::lean_dec(v___x_3936_);
                            v___x_3939_ = leanh::lean_box(0);
                            v_isShared_3940_ = v_isSharedCheck_4091_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3933_);
                        leanh::lean_dec_ref(v_e_3920_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3928_ = leanh::lean_box(0);
                v___x_3929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                return v___x_3929_;
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3937_) == 1 {
                    v_val_3941_ = leanh::lean_ctor_get(v_a_3937_, 0);
                    v_isSharedCheck_3983_ = (!leanh::lean_is_exclusive(v_a_3937_)) as u8;
                    if v_isSharedCheck_3983_ == 0 {
                        v___x_3943_ = v_a_3937_;
                        v_isShared_3944_ = v_isSharedCheck_3983_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3941_);
                        leanh::lean_dec(v_a_3937_);
                        v___x_3943_ = leanh::lean_box(0);
                        v_isShared_3944_ = v_isSharedCheck_3983_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3939_);
                    leanh::lean_dec(v_a_3937_);
                    v___x_3984_ = lean_st_ref_get(v___y_3925_);
                    if v_alsoCasesOn_3921_ == 0 {
                        leanh::lean_dec(v___x_3984_);
                        leanh::lean_dec(v_us_3935_);
                        leanh::lean_dec(v_declName_3934_);
                        leanh::lean_dec_ref(v_e_3920_);
                        state = 1;
                        continue;
                    } else {
                        v_env_3985_ = leanh::lean_ctor_get(v___x_3984_, 0);
                        leanh::lean_inc_ref(v_env_3985_);
                        leanh::lean_dec(v___x_3984_);
                        leanh::lean_inc(v_declName_3934_);
                        v___x_3986_ = l_Lean_isCasesOnRecursor(v_env_3985_, v_declName_3934_);
                        if v___x_3986_ == 0 {
                            leanh::lean_dec(v_us_3935_);
                            leanh::lean_dec(v_declName_3934_);
                            leanh::lean_dec_ref(v_e_3920_);
                            state = 1;
                            continue;
                        } else {
                            v_indName_3987_ = l_Lean_Name_getPrefix(v_declName_3934_);
                            v___x_3988_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_3987_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
                            if leanh::lean_obj_tag(v___x_3988_) == 0 {
                                v_a_3989_ = leanh::lean_ctor_get(v___x_3988_, 0);
                                v_isSharedCheck_4082_ =
                                    (!leanh::lean_is_exclusive(v___x_3988_)) as u8;
                                if v_isSharedCheck_4082_ == 0 {
                                    v___x_3991_ = v___x_3988_;
                                    v_isShared_3992_ = v_isSharedCheck_4082_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3989_);
                                    leanh::lean_dec(v___x_3988_);
                                    v___x_3991_ = leanh::lean_box(0);
                                    v_isShared_3992_ = v_isSharedCheck_4082_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_us_3935_);
                                leanh::lean_dec(v_declName_3934_);
                                leanh::lean_dec_ref(v_e_3920_);
                                v_a_4083_ = leanh::lean_ctor_get(v___x_3988_, 0);
                                v_isSharedCheck_4090_ =
                                    (!leanh::lean_is_exclusive(v___x_3988_)) as u8;
                                if v_isSharedCheck_4090_ == 0 {
                                    v___x_4085_ = v___x_3988_;
                                    v_isShared_4086_ = v_isSharedCheck_4090_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4083_);
                                    leanh::lean_dec(v___x_3988_);
                                    v___x_4085_ = leanh::lean_box(0);
                                    v_isShared_4086_ = v_isSharedCheck_4090_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v_dummy_3945_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
                v_nargs_3946_ = l_Lean_Expr_getAppNumArgs(v_e_3920_);
                leanh::lean_inc(v_nargs_3946_);
                v___x_3947_ = lean_mk_array(v_nargs_3946_, v_dummy_3945_);
                v___x_3948_ = leanh::lean_unsigned_to_nat(1);
                v___x_3949_ = lean_nat_sub(v_nargs_3946_, v___x_3948_);
                leanh::lean_dec(v_nargs_3946_);
                v_args_3950_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_3920_,
                    v___x_3947_,
                    v___x_3949_,
                );
                v___x_3951_ = lean_array_get_size(v_args_3950_);
                v___x_3952_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3941_);
                v___x_3953_ = lean_nat_dec_lt(v___x_3951_, v___x_3952_);
                leanh::lean_dec(v___x_3952_);
                if v___x_3953_ == 0 {
                    v_numParams_3954_ = leanh::lean_ctor_get(v_val_3941_, 0);
                    v_numDiscrs_3955_ = leanh::lean_ctor_get(v_val_3941_, 1);
                    v___x_3956_ = lean_array_mk(v_us_3935_);
                    v___x_3957_ = leanh::lean_unsigned_to_nat(0);
                    leanh::lean_inc(v_numParams_3954_);
                    v___x_3958_ =
                        l_Array_extract___redArg(v_args_3950_, v___x_3957_, v_numParams_3954_);
                    v___x_3959_ = l_Lean_instInhabitedExpr;
                    v___x_3960_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3941_);
                    v___x_3961_ = lean_array_get(v___x_3959_, v_args_3950_, v___x_3960_);
                    leanh::lean_dec(v___x_3960_);
                    v___x_3962_ = lean_nat_add(v_numParams_3954_, v___x_3948_);
                    v___x_3963_ = lean_nat_add(v___x_3962_, v_numDiscrs_3955_);
                    leanh::lean_inc(v___x_3963_);
                    leanh::lean_inc_ref_n(v_args_3950_, 2);
                    v___x_3964_ =
                        l_Array_toSubarray___redArg(v_args_3950_, v___x_3962_, v___x_3963_);
                    v___x_3965_ = l_Subarray_copy___redArg(v___x_3964_);
                    v___x_3966_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3941_);
                    v___x_3967_ = lean_nat_add(v___x_3963_, v___x_3966_);
                    leanh::lean_dec(v___x_3966_);
                    leanh::lean_inc(v___x_3967_);
                    v___x_3968_ =
                        l_Array_toSubarray___redArg(v_args_3950_, v___x_3963_, v___x_3967_);
                    v___x_3969_ = l_Subarray_copy___redArg(v___x_3968_);
                    v___x_3970_ =
                        l_Array_toSubarray___redArg(v_args_3950_, v___x_3967_, v___x_3951_);
                    v___x_3971_ = l_Subarray_copy___redArg(v___x_3970_);
                    v___x_3972_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v___x_3972_, 0, v_val_3941_);
                    leanh::lean_ctor_set(v___x_3972_, 1, v_declName_3934_);
                    leanh::lean_ctor_set(v___x_3972_, 2, v___x_3956_);
                    leanh::lean_ctor_set(v___x_3972_, 3, v___x_3958_);
                    leanh::lean_ctor_set(v___x_3972_, 4, v___x_3961_);
                    leanh::lean_ctor_set(v___x_3972_, 5, v___x_3965_);
                    leanh::lean_ctor_set(v___x_3972_, 6, v___x_3969_);
                    leanh::lean_ctor_set(v___x_3972_, 7, v___x_3971_);
                    if v_isShared_3944_ == 0 {
                        leanh::lean_ctor_set(v___x_3943_, 0, v___x_3972_);
                        v___x_3974_ = v___x_3943_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3978_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3972_);
                        v___x_3974_ = v_reuseFailAlloc_3978_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_args_3950_);
                    leanh::lean_del_object(v___x_3943_);
                    leanh::lean_dec(v_val_3941_);
                    leanh::lean_dec(v_us_3935_);
                    leanh::lean_dec(v_declName_3934_);
                    v___x_3979_ = leanh::lean_box(0);
                    if v_isShared_3940_ == 0 {
                        leanh::lean_ctor_set(v___x_3939_, 0, v___x_3979_);
                        v___x_3981_ = v___x_3939_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3982_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
                        v___x_3981_ = v_reuseFailAlloc_3982_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3940_ == 0 {
                    leanh::lean_ctor_set(v___x_3939_, 0, v___x_3974_);
                    v___x_3976_ = v___x_3939_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3976_;
            }
            6 => {
                return v___x_3981_;
            }
            7 => {
                if leanh::lean_obj_tag(v_a_3989_) == 5 {
                    v_val_3993_ = leanh::lean_ctor_get(v_a_3989_, 0);
                    v_isSharedCheck_4077_ = (!leanh::lean_is_exclusive(v_a_3989_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_3995_ = v_a_3989_;
                        v_isShared_3996_ = v_isSharedCheck_4077_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3993_);
                        leanh::lean_dec(v_a_3989_);
                        v___x_3995_ = leanh::lean_box(0);
                        v_isShared_3996_ = v_isSharedCheck_4077_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3989_);
                    leanh::lean_dec(v_us_3935_);
                    leanh::lean_dec(v_declName_3934_);
                    leanh::lean_dec_ref(v_e_3920_);
                    v___x_4078_ = leanh::lean_box(0);
                    if v_isShared_3992_ == 0 {
                        leanh::lean_ctor_set(v___x_3991_, 0, v___x_4078_);
                        v___x_4080_ = v___x_3991_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4081_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4078_);
                        v___x_4080_ = v_reuseFailAlloc_4081_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                v_toConstantVal_3997_ = leanh::lean_ctor_get(v_val_3993_, 0);
                leanh::lean_inc_ref(v_toConstantVal_3997_);
                v_numParams_3998_ = leanh::lean_ctor_get(v_val_3993_, 1);
                leanh::lean_inc(v_numParams_3998_);
                v_numIndices_3999_ = leanh::lean_ctor_get(v_val_3993_, 2);
                leanh::lean_inc(v_numIndices_3999_);
                v_ctors_4000_ = leanh::lean_ctor_get(v_val_3993_, 4);
                leanh::lean_inc(v_ctors_4000_);
                v_nargs_4001_ = l_Lean_Expr_getAppNumArgs(v_e_3920_);
                v_dummy_4002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
                leanh::lean_inc(v_nargs_4001_);
                v___x_4003_ = lean_mk_array(v_nargs_4001_, v_dummy_4002_);
                v___x_4004_ = leanh::lean_unsigned_to_nat(1);
                v___x_4005_ = lean_nat_sub(v_nargs_4001_, v___x_4004_);
                leanh::lean_dec(v_nargs_4001_);
                v_args_4006_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_3920_,
                    v___x_4003_,
                    v___x_4005_,
                );
                v___x_4007_ = lean_nat_add(v_numParams_3998_, v___x_4004_);
                v___x_4008_ = lean_nat_add(v___x_4007_, v_numIndices_3999_);
                v___x_4009_ = lean_nat_add(v___x_4008_, v___x_4004_);
                leanh::lean_dec(v___x_4008_);
                v___x_4010_ = l_Lean_InductiveVal_numCtors(v_val_3993_);
                leanh::lean_dec_ref(v_val_3993_);
                v___x_4011_ = lean_nat_add(v___x_4009_, v___x_4010_);
                leanh::lean_dec(v___x_4010_);
                v___x_4012_ = lean_array_get_size(v_args_4006_);
                v___x_4013_ = lean_nat_dec_le(v___x_4011_, v___x_4012_);
                if v___x_4013_ == 0 {
                    leanh::lean_dec(v___x_4011_);
                    leanh::lean_dec(v___x_4009_);
                    leanh::lean_dec(v___x_4007_);
                    leanh::lean_dec_ref(v_args_4006_);
                    leanh::lean_dec(v_ctors_4000_);
                    leanh::lean_dec(v_numIndices_3999_);
                    leanh::lean_dec(v_numParams_3998_);
                    leanh::lean_dec_ref(v_toConstantVal_3997_);
                    leanh::lean_del_object(v___x_3995_);
                    leanh::lean_dec(v_us_3935_);
                    leanh::lean_dec(v_declName_3934_);
                    v___x_4014_ = leanh::lean_box(0);
                    if v_isShared_3992_ == 0 {
                        leanh::lean_ctor_set(v___x_3991_, 0, v___x_4014_);
                        v___x_4016_ = v___x_3991_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4017_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4014_);
                        v___x_4016_ = v_reuseFailAlloc_4017_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3991_);
                    v___x_4018_ = leanh::lean_unsigned_to_nat(0);
                    leanh::lean_inc(v_numParams_3998_);
                    leanh::lean_inc_ref_n(v_args_4006_, 3);
                    v_params_4019_ =
                        l_Array_toSubarray___redArg(v_args_4006_, v___x_4018_, v_numParams_3998_);
                    v___x_4020_ = l_Lean_instInhabitedExpr;
                    v_motive_4021_ = lean_array_get(v___x_4020_, v_args_4006_, v_numParams_3998_);
                    leanh::lean_dec(v_numParams_3998_);
                    leanh::lean_inc(v___x_4009_);
                    v_discrs_4022_ =
                        l_Array_toSubarray___redArg(v_args_4006_, v___x_4007_, v___x_4009_);
                    v___x_4023_ = lean_nat_add(v_numIndices_3999_, v___x_4004_);
                    leanh::lean_dec(v_numIndices_3999_);
                    v___x_4024_ = leanh::lean_box(0);
                    v_discrInfos_4025_ = lean_mk_array(v___x_4023_, v___x_4024_);
                    leanh::lean_inc(v___x_4011_);
                    v_alts_4026_ =
                        l_Array_toSubarray___redArg(v_args_4006_, v___x_4009_, v___x_4011_);
                    v___x_4076_ = lean_nat_dec_le(v___x_4011_, v___x_4018_);
                    if v___x_4076_ == 0 {
                        v_lower_4068_ = v___x_4011_;
                        v_upper_4069_ = v___x_4012_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4011_);
                        v_lower_4068_ = v___x_4018_;
                        v_upper_4069_ = v___x_4012_;
                        state = 16;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_4016_;
            }
            10 => {
                v___x_4030_ = lean_array_mk(v_ctors_4000_);
                v_sz_4031_ = lean_array_size(v___x_4030_);
                v___x_4032_ = 0usize;
                v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_4031_, v___x_4032_, v___x_4030_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
                if leanh::lean_obj_tag(v___x_4033_) == 0 {
                    v_a_4034_ = leanh::lean_ctor_get(v___x_4033_, 0);
                    v_isSharedCheck_4058_ = (!leanh::lean_is_exclusive(v___x_4033_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4036_ = v___x_4033_;
                        v_isShared_4037_ = v_isSharedCheck_4058_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4034_);
                        leanh::lean_dec(v___x_4033_);
                        v___x_4036_ = leanh::lean_box(0);
                        v_isShared_4037_ = v_isSharedCheck_4058_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_4029_);
                    leanh::lean_dec_ref(v___y_4028_);
                    leanh::lean_dec_ref(v_alts_4026_);
                    leanh::lean_dec_ref(v_discrInfos_4025_);
                    leanh::lean_dec_ref(v_discrs_4022_);
                    leanh::lean_dec(v_motive_4021_);
                    leanh::lean_dec_ref(v_params_4019_);
                    leanh::lean_del_object(v___x_3995_);
                    leanh::lean_dec(v_us_3935_);
                    leanh::lean_dec(v_declName_3934_);
                    v_a_4059_ = leanh::lean_ctor_get(v___x_4033_, 0);
                    v_isSharedCheck_4066_ = (!leanh::lean_is_exclusive(v___x_4033_)) as u8;
                    if v_isSharedCheck_4066_ == 0 {
                        v___x_4061_ = v___x_4033_;
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4059_);
                        leanh::lean_dec(v___x_4033_);
                        v___x_4061_ = leanh::lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_start_4038_ = leanh::lean_ctor_get(v_params_4019_, 1);
                leanh::lean_inc(v_start_4038_);
                v_stop_4039_ = leanh::lean_ctor_get(v_params_4019_, 2);
                leanh::lean_inc(v_stop_4039_);
                v_start_4040_ = leanh::lean_ctor_get(v_discrs_4022_, 1);
                leanh::lean_inc(v_start_4040_);
                v_stop_4041_ = leanh::lean_ctor_get(v_discrs_4022_, 2);
                leanh::lean_inc(v_stop_4041_);
                v___x_4042_ = lean_nat_sub(v_stop_4039_, v_start_4038_);
                leanh::lean_dec(v_start_4038_);
                leanh::lean_dec(v_stop_4039_);
                v___x_4043_ = lean_nat_sub(v_stop_4041_, v_start_4040_);
                leanh::lean_dec(v_start_4040_);
                leanh::lean_dec(v_stop_4041_);
                v___x_4044_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
                v___x_4045_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_4045_, 0, v___x_4042_);
                leanh::lean_ctor_set(v___x_4045_, 1, v___x_4043_);
                leanh::lean_ctor_set(v___x_4045_, 2, v_a_4034_);
                leanh::lean_ctor_set(v___x_4045_, 3, v___y_4029_);
                leanh::lean_ctor_set(v___x_4045_, 4, v_discrInfos_4025_);
                leanh::lean_ctor_set(v___x_4045_, 5, v___x_4044_);
                v___x_4046_ = lean_array_mk(v_us_3935_);
                v___x_4047_ = l_Subarray_copy___redArg(v_params_4019_);
                v___x_4048_ = l_Subarray_copy___redArg(v_discrs_4022_);
                v___x_4049_ = l_Subarray_copy___redArg(v_alts_4026_);
                v___x_4050_ = l_Subarray_copy___redArg(v___y_4028_);
                v___x_4051_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                leanh::lean_ctor_set(v___x_4051_, 0, v___x_4045_);
                leanh::lean_ctor_set(v___x_4051_, 1, v_declName_3934_);
                leanh::lean_ctor_set(v___x_4051_, 2, v___x_4046_);
                leanh::lean_ctor_set(v___x_4051_, 3, v___x_4047_);
                leanh::lean_ctor_set(v___x_4051_, 4, v_motive_4021_);
                leanh::lean_ctor_set(v___x_4051_, 5, v___x_4048_);
                leanh::lean_ctor_set(v___x_4051_, 6, v___x_4049_);
                leanh::lean_ctor_set(v___x_4051_, 7, v___x_4050_);
                if v_isShared_3996_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3995_, 1);
                    leanh::lean_ctor_set(v___x_3995_, 0, v___x_4051_);
                    v___x_4053_ = v___x_3995_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4051_);
                    v___x_4053_ = v_reuseFailAlloc_4057_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4037_ == 0 {
                    leanh::lean_ctor_set(v___x_4036_, 0, v___x_4053_);
                    v___x_4055_ = v___x_4036_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
                    v___x_4055_ = v_reuseFailAlloc_4056_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4055_;
            }
            14 => {
                if v_isShared_4062_ == 0 {
                    v___x_4064_ = v___x_4061_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4064_;
            }
            16 => {
                v_levelParams_4070_ = leanh::lean_ctor_get(v_toConstantVal_3997_, 1);
                leanh::lean_inc(v_levelParams_4070_);
                leanh::lean_dec_ref(v_toConstantVal_3997_);
                v___x_4071_ =
                    l_Array_toSubarray___redArg(v_args_4006_, v_lower_4068_, v_upper_4069_);
                v___x_4072_ = l_List_lengthTR___redArg(v_levelParams_4070_);
                leanh::lean_dec(v_levelParams_4070_);
                v___x_4073_ = l_List_lengthTR___redArg(v_us_3935_);
                v___x_4074_ = lean_nat_dec_eq(v___x_4072_, v___x_4073_);
                leanh::lean_dec(v___x_4073_);
                leanh::lean_dec(v___x_4072_);
                if v___x_4074_ == 0 {
                    v___x_4075_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3;
                    v___y_4028_ = v___x_4071_;
                    v___y_4029_ = v___x_4075_;
                    state = 10;
                    continue;
                } else {
                    v___y_4028_ = v___x_4071_;
                    v___y_4029_ = v___x_4024_;
                    state = 10;
                    continue;
                }
            }
            17 => {
                return v___x_4080_;
            }
            18 => {
                if v_isShared_4086_ == 0 {
                    v___x_4088_ = v___x_4085_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4089_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
                    v___x_4088_ = v_reuseFailAlloc_4089_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(
    mut v_e_4092_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_alsoCasesOn_boxed_4099_: u8 = 0;
    let mut v_res_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_4099_ = (leanh::lean_unbox(v_alsoCasesOn_4093_) as u8);
    v_res_4100_ =
        l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(
            v_e_4092_,
            v_alsoCasesOn_boxed_4099_,
            v___y_4094_,
            v___y_4095_,
            v___y_4096_,
            v___y_4097_,
        );
    leanh::lean_dec(v___y_4097_);
    leanh::lean_dec_ref(v___y_4096_);
    leanh::lean_dec(v___y_4095_);
    leanh::lean_dec_ref(v___y_4094_);
    return v_res_4100_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(
    mut v_e_4101_: *mut leanh::LeanObject,
    mut v_a_4102_: *mut leanh::LeanObject,
    mut v_a_4103_: *mut leanh::LeanObject,
    mut v_a_4104_: *mut leanh::LeanObject,
    mut v_a_4105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: u8 = 0;
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v_val_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_a_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4107_ =
                    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1;
                v___x_4108_ = l_Lean_Expr_isAppOf(v_e_4101_, v___x_4107_);
                if v___x_4108_ == 0 {
                    v___x_4109_ =
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1;
                    v___x_4110_ = l_Lean_Expr_isAppOf(v_e_4101_, v___x_4109_);
                    if v___x_4110_ == 0 {
                        v___x_4111_ = 1;
                        v___x_4112_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_4101_, v___x_4111_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
                        if leanh::lean_obj_tag(v___x_4112_) == 0 {
                            v_a_4113_ = leanh::lean_ctor_get(v___x_4112_, 0);
                            v_isSharedCheck_4133_ =
                                (!leanh::lean_is_exclusive(v___x_4112_)) as u8;
                            if v_isSharedCheck_4133_ == 0 {
                                v___x_4115_ = v___x_4112_;
                                v_isShared_4116_ = v_isSharedCheck_4133_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4113_);
                                leanh::lean_dec(v___x_4112_);
                                v___x_4115_ = leanh::lean_box(0);
                                v_isShared_4116_ = v_isSharedCheck_4133_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4134_ = leanh::lean_ctor_get(v___x_4112_, 0);
                            v_isSharedCheck_4141_ =
                                (!leanh::lean_is_exclusive(v___x_4112_)) as u8;
                            if v_isSharedCheck_4141_ == 0 {
                                v___x_4136_ = v___x_4112_;
                                v_isShared_4137_ = v_isSharedCheck_4141_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4134_);
                                leanh::lean_dec(v___x_4112_);
                                v___x_4136_ = leanh::lean_box(0);
                                v_isShared_4137_ = v_isSharedCheck_4141_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_4142_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4142_, 0, v_e_4101_);
                        v___x_4143_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4143_, 0, v___x_4142_);
                        v___x_4144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4144_, 0, v___x_4143_);
                        return v___x_4144_;
                    }
                } else {
                    v___x_4145_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4145_, 0, v_e_4101_);
                    v___x_4146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4146_, 0, v___x_4145_);
                    v___x_4147_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4147_, 0, v___x_4146_);
                    return v___x_4147_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4113_) == 1 {
                    v_val_4117_ = leanh::lean_ctor_get(v_a_4113_, 0);
                    v_isSharedCheck_4128_ = (!leanh::lean_is_exclusive(v_a_4113_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4119_ = v_a_4113_;
                        v_isShared_4120_ = v_isSharedCheck_4128_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4117_);
                        leanh::lean_dec(v_a_4113_);
                        v___x_4119_ = leanh::lean_box(0);
                        v_isShared_4120_ = v_isSharedCheck_4128_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4113_);
                    v___x_4129_ = leanh::lean_box(0);
                    if v_isShared_4116_ == 0 {
                        leanh::lean_ctor_set(v___x_4115_, 0, v___x_4129_);
                        v___x_4131_ = v___x_4115_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4132_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
                        v___x_4131_ = v_reuseFailAlloc_4132_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4121_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4121_, 0, v_val_4117_);
                if v_isShared_4120_ == 0 {
                    leanh::lean_ctor_set(v___x_4119_, 0, v___x_4121_);
                    v___x_4123_ = v___x_4119_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4121_);
                    v___x_4123_ = v_reuseFailAlloc_4127_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4116_ == 0 {
                    leanh::lean_ctor_set(v___x_4115_, 0, v___x_4123_);
                    v___x_4125_ = v___x_4115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
                    v___x_4125_ = v_reuseFailAlloc_4126_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4125_;
            }
            5 => {
                return v___x_4131_;
            }
            6 => {
                if v_isShared_4137_ == 0 {
                    v___x_4139_ = v___x_4136_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(
    mut v_e_4148_: *mut leanh::LeanObject,
    mut v_a_4149_: *mut leanh::LeanObject,
    mut v_a_4150_: *mut leanh::LeanObject,
    mut v_a_4151_: *mut leanh::LeanObject,
    mut v_a_4152_: *mut leanh::LeanObject,
    mut v_a_4153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(
        v_e_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_,
    );
    leanh::lean_dec(v_a_4152_);
    leanh::lean_dec_ref(v_a_4151_);
    leanh::lean_dec(v_a_4150_);
    leanh::lean_dec_ref(v_a_4149_);
    return v_res_4154_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(
    mut v_declName_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
    mut v___y_4159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4161_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_4155_, v___y_4159_);
    return v___x_4161_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(
    mut v_declName_4162_: *mut leanh::LeanObject,
    mut v___y_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4168_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
    leanh::lean_dec(v___y_4166_);
    leanh::lean_dec_ref(v___y_4165_);
    leanh::lean_dec(v___y_4164_);
    leanh::lean_dec_ref(v___y_4163_);
    return v_res_4168_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4169_: *mut leanh::LeanObject,
    mut v_constName_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: *mut leanh::LeanObject,
    mut v___y_4172_: *mut leanh::LeanObject,
    mut v___y_4173_: *mut leanh::LeanObject,
    mut v___y_4174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
    return v___x_4176_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4177_: *mut leanh::LeanObject,
    mut v_constName_4178_: *mut leanh::LeanObject,
    mut v___y_4179_: *mut leanh::LeanObject,
    mut v___y_4180_: *mut leanh::LeanObject,
    mut v___y_4181_: *mut leanh::LeanObject,
    mut v___y_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4184_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_4177_, v_constName_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
    leanh::lean_dec(v___y_4182_);
    leanh::lean_dec_ref(v___y_4181_);
    leanh::lean_dec(v___y_4180_);
    leanh::lean_dec_ref(v___y_4179_);
    return v_res_4184_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_4185_: *mut leanh::LeanObject,
    mut v_ref_4186_: *mut leanh::LeanObject,
    mut v_constName_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4193_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_4186_, v_constName_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
    return v___x_4193_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_4194_: *mut leanh::LeanObject,
    mut v_ref_4195_: *mut leanh::LeanObject,
    mut v_constName_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4194_, v_ref_4195_, v_constName_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
    leanh::lean_dec(v___y_4200_);
    leanh::lean_dec_ref(v___y_4199_);
    leanh::lean_dec(v___y_4198_);
    leanh::lean_dec_ref(v___y_4197_);
    leanh::lean_dec(v_ref_4195_);
    return v_res_4202_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_4203_: *mut leanh::LeanObject,
    mut v_ref_4204_: *mut leanh::LeanObject,
    mut v_msg_4205_: *mut leanh::LeanObject,
    mut v_declHint_4206_: *mut leanh::LeanObject,
    mut v___y_4207_: *mut leanh::LeanObject,
    mut v___y_4208_: *mut leanh::LeanObject,
    mut v___y_4209_: *mut leanh::LeanObject,
    mut v___y_4210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4212_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_4204_, v_msg_4205_, v_declHint_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_4213_: *mut leanh::LeanObject,
    mut v_ref_4214_: *mut leanh::LeanObject,
    mut v_msg_4215_: *mut leanh::LeanObject,
    mut v_declHint_4216_: *mut leanh::LeanObject,
    mut v___y_4217_: *mut leanh::LeanObject,
    mut v___y_4218_: *mut leanh::LeanObject,
    mut v___y_4219_: *mut leanh::LeanObject,
    mut v___y_4220_: *mut leanh::LeanObject,
    mut v___y_4221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4222_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_4213_, v_ref_4214_, v_msg_4215_, v_declHint_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
    leanh::lean_dec(v___y_4220_);
    leanh::lean_dec_ref(v___y_4219_);
    leanh::lean_dec(v___y_4218_);
    leanh::lean_dec_ref(v___y_4217_);
    leanh::lean_dec(v_ref_4214_);
    return v_res_4222_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(
    mut v_msg_4223_: *mut leanh::LeanObject,
    mut v_declHint_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4223_, v_declHint_4224_, v___y_4228_);
    return v___x_4230_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(
    mut v_msg_4231_: *mut leanh::LeanObject,
    mut v_declHint_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
    mut v___y_4237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4238_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_4231_, v_declHint_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
    leanh::lean_dec(v___y_4236_);
    leanh::lean_dec_ref(v___y_4235_);
    leanh::lean_dec(v___y_4234_);
    leanh::lean_dec_ref(v___y_4233_);
    return v_res_4238_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(
    mut v_00_u03b1_4239_: *mut leanh::LeanObject,
    mut v_ref_4240_: *mut leanh::LeanObject,
    mut v_msg_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_4240_, v_msg_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
    return v___x_4247_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_4248_: *mut leanh::LeanObject,
    mut v_ref_4249_: *mut leanh::LeanObject,
    mut v_msg_4250_: *mut leanh::LeanObject,
    mut v___y_4251_: *mut leanh::LeanObject,
    mut v___y_4252_: *mut leanh::LeanObject,
    mut v___y_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4256_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_4248_, v_ref_4249_, v_msg_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
    leanh::lean_dec(v___y_4254_);
    leanh::lean_dec_ref(v___y_4253_);
    leanh::lean_dec(v___y_4252_);
    leanh::lean_dec_ref(v___y_4251_);
    leanh::lean_dec(v_ref_4249_);
    return v_res_4256_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(
    mut v_00_u03b1_4257_: *mut leanh::LeanObject,
    mut v_msg_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
    mut v___y_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
    mut v___y_4262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4264_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
    return v___x_4264_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b1_4265_: *mut leanh::LeanObject,
    mut v_msg_4266_: *mut leanh::LeanObject,
    mut v___y_4267_: *mut leanh::LeanObject,
    mut v___y_4268_: *mut leanh::LeanObject,
    mut v___y_4269_: *mut leanh::LeanObject,
    mut v___y_4270_: *mut leanh::LeanObject,
    mut v___y_4271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4272_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_4265_, v_msg_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
    leanh::lean_dec(v___y_4270_);
    leanh::lean_dec_ref(v___y_4269_);
    leanh::lean_dec(v___y_4268_);
    leanh::lean_dec_ref(v___y_4267_);
    return v_res_4272_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4274_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0;
    v___x_4275_ = l_Lean_stringToMessageData(v___x_4274_);
    return v___x_4275_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_rwIfOrMatcher(
    mut v_idx_4276_: *mut leanh::LeanObject,
    mut v_e_4277_: *mut leanh::LeanObject,
    mut v_a_4278_: *mut leanh::LeanObject,
    mut v_a_4279_: *mut leanh::LeanObject,
    mut v_a_4280_: *mut leanh::LeanObject,
    mut v_a_4281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v___y_4303_: u8 = 0;
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4313_ =
                    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1;
                v___x_4314_ = l_Lean_Expr_isAppOf(v_e_4277_, v___x_4313_);
                if v___x_4314_ == 0 {
                    v___x_4315_ =
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1;
                    v___x_4316_ = l_Lean_Expr_isAppOf(v_e_4277_, v___x_4315_);
                    v___y_4303_ = v___x_4316_;
                    state = 4;
                    continue;
                } else {
                    v___y_4303_ = v___x_4314_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_4284_);
                v___x_4285_ = l_Lean_Meta_findLocalDeclWithType_x3f(
                    v___y_4284_,
                    v_a_4278_,
                    v_a_4279_,
                    v_a_4280_,
                    v_a_4281_,
                );
                if leanh::lean_obj_tag(v___x_4285_) == 0 {
                    v_a_4286_ = leanh::lean_ctor_get(v___x_4285_, 0);
                    leanh::lean_inc(v_a_4286_);
                    leanh::lean_dec_ref_known(v___x_4285_, 1);
                    if leanh::lean_obj_tag(v_a_4286_) == 1 {
                        leanh::lean_dec_ref(v___y_4284_);
                        v_val_4287_ = leanh::lean_ctor_get(v_a_4286_, 0);
                        leanh::lean_inc(v_val_4287_);
                        leanh::lean_dec_ref_known(v_a_4286_, 1);
                        v___x_4288_ = l_Lean_mkFVar(v_val_4287_);
                        v___x_4289_ = l_Lean_Meta_rwIfWith(
                            v___x_4288_,
                            v_e_4277_,
                            v_a_4278_,
                            v_a_4279_,
                            v_a_4280_,
                            v_a_4281_,
                        );
                        return v___x_4289_;
                    } else {
                        leanh::lean_dec(v_a_4286_);
                        leanh::lean_dec_ref(v_e_4277_);
                        v___x_4290_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1,
                        );
                        v___x_4291_ = l_Lean_MessageData_ofExpr(v___y_4284_);
                        v___x_4292_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4292_, 0, v___x_4290_);
                        leanh::lean_ctor_set(v___x_4292_, 1, v___x_4291_);
                        v___x_4293_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_4292_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
                        return v___x_4293_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_4284_);
                    leanh::lean_dec_ref(v_e_4277_);
                    v_a_4294_ = leanh::lean_ctor_get(v___x_4285_, 0);
                    v_isSharedCheck_4301_ = (!leanh::lean_is_exclusive(v___x_4285_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4296_ = v___x_4285_;
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4294_);
                        leanh::lean_dec(v___x_4285_);
                        v___x_4296_ = leanh::lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4297_ == 0 {
                    v___x_4299_ = v___x_4296_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
                    v___x_4299_ = v_reuseFailAlloc_4300_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4299_;
            }
            4 => {
                if v___y_4303_ == 0 {
                    v___x_4304_ = l_Lean_Meta_rwMatcher(
                        v_idx_4276_,
                        v_e_4277_,
                        v_a_4278_,
                        v_a_4279_,
                        v_a_4280_,
                        v_a_4281_,
                    );
                    return v___x_4304_;
                } else {
                    v___x_4305_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4306_ = l_Lean_Expr_getAppNumArgs(v_e_4277_);
                    v___x_4307_ = lean_nat_sub(v___x_4306_, v___x_4305_);
                    leanh::lean_dec(v___x_4306_);
                    v___x_4308_ = lean_nat_sub(v___x_4307_, v___x_4305_);
                    leanh::lean_dec(v___x_4307_);
                    v_c_4309_ = l_Lean_Expr_getRevArg_x21(v_e_4277_, v___x_4308_);
                    v___x_4310_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4311_ = lean_nat_dec_eq(v_idx_4276_, v___x_4310_);
                    leanh::lean_dec(v_idx_4276_);
                    if v___x_4311_ == 0 {
                        v___x_4312_ = l_Lean_mkNot(v_c_4309_);
                        v___y_4284_ = v___x_4312_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4284_ = v_c_4309_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(
    mut v_idx_4317_: *mut leanh::LeanObject,
    mut v_e_4318_: *mut leanh::LeanObject,
    mut v_a_4319_: *mut leanh::LeanObject,
    mut v_a_4320_: *mut leanh::LeanObject,
    mut v_a_4321_: *mut leanh::LeanObject,
    mut v_a_4322_: *mut leanh::LeanObject,
    mut v_a_4323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(
        v_idx_4317_,
        v_e_4318_,
        v_a_4319_,
        v_a_4320_,
        v_a_4321_,
        v_a_4322_,
    );
    leanh::lean_dec(v_a_4322_);
    leanh::lean_dec_ref(v_a_4321_);
    leanh::lean_dec(v_a_4320_);
    leanh::lean_dec_ref(v_a_4319_);
    return v_res_4324_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default =
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default);
    l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo =
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_VCGen_Split(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
}