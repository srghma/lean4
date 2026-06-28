// Lean compiler output
// Module: Lean.Elab.Tactic.Do.VCGen.Split
// Imports: Lean.Meta.Tactic.Simp.Types Lean.Meta.Match.MatcherApp.Transform Lean.Data.Array Lean.Meta.Match.Rewrite Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Assumption
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
    l_Array_extract___redArg, l_Lean_Name_mkStr1, l_Lean_replaceRef, l_List_lengthTR___redArg,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate_rev;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_5, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value)
            as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value
        ) as *mut LeanObject,
        18356704233129443855 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value
        ) as *mut LeanObject,
        18388690793488095770 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        3844805874353431675 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value
        ) as *mut LeanObject,
        13886804137793424261 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value
        ) as *mut LeanObject,
        4342836574150310743 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value
        ) as *mut LeanObject,
        8391571994004792969 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__0_value
        ) as *mut LeanObject,
        6207155323350122738 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__0_value
        ) as *mut LeanObject,
        11893266011724725697 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_etaExpand___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__7_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__3_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__4_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__5_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9_value:
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
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__8_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__6_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value)
            as *mut LeanObject,
        388469914488256294 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value
        ) as *mut LeanObject,
        17863078355054839409 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value
        ) as *mut LeanObject,
        16879624741230498429 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value
        ) as *mut LeanObject,
        8738205681931236784 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_MatcherApp_toExpr as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Expr_isFVar___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 97, 116, 99, 104, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 112, 114, 111,
            111, 102, 32, 102, 111, 114, 32, 105, 102, 32, 99, 111, 110, 100, 105, 116, 105, 111,
            110, 32, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(
    mut v_x_2163_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2163_) {
        0 => {
            let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
            v___x_2164_ = lean_unsigned_to_nat(0);
            return v___x_2164_;
        }
        1 => {
            let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
            v___x_2165_ = lean_unsigned_to_nat(1);
            return v___x_2165_;
        }
        _ => {
            let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
            v___x_2166_ = lean_unsigned_to_nat(2);
            return v___x_2166_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___boxed(
    mut v_x_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2168_: *mut LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(v_x_2167_);
    lean_dec_ref(v_x_2167_);
    return v_res_2168_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(
    mut v_t_2169_: *mut LeanObject,
    mut v_k_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    v_e_2171_ = lean_ctor_get(v_t_2169_, 0);
    lean_inc_ref(v_e_2171_);
    lean_dec_ref(v_t_2169_);
    v___x_2172_ = lean_apply_1(v_k_2170_, v_e_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(
    mut v_motive_2173_: *mut LeanObject,
    mut v_ctorIdx_2174_: *mut LeanObject,
    mut v_t_2175_: *mut LeanObject,
    mut v_h_2176_: *mut LeanObject,
    mut v_k_2177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    v___x_2178_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2175_, v_k_2177_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(
    mut v_motive_2179_: *mut LeanObject,
    mut v_ctorIdx_2180_: *mut LeanObject,
    mut v_t_2181_: *mut LeanObject,
    mut v_h_2182_: *mut LeanObject,
    mut v_k_2183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2184_: *mut LeanObject = core::ptr::null_mut();
    v_res_2184_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(
        v_motive_2179_,
        v_ctorIdx_2180_,
        v_t_2181_,
        v_h_2182_,
        v_k_2183_,
    );
    lean_dec(v_ctorIdx_2180_);
    return v_res_2184_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(
    mut v_t_2185_: *mut LeanObject,
    mut v_ite_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2185_, v_ite_2186_);
    return v___x_2187_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(
    mut v_motive_2188_: *mut LeanObject,
    mut v_t_2189_: *mut LeanObject,
    mut v_h_2190_: *mut LeanObject,
    mut v_ite_2191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    v___x_2192_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2189_, v_ite_2191_);
    return v___x_2192_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(
    mut v_t_2193_: *mut LeanObject,
    mut v_dite_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2193_, v_dite_2194_);
    return v___x_2195_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(
    mut v_motive_2196_: *mut LeanObject,
    mut v_t_2197_: *mut LeanObject,
    mut v_h_2198_: *mut LeanObject,
    mut v_dite_2199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    v___x_2200_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2197_, v_dite_2199_);
    return v___x_2200_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(
    mut v_t_2201_: *mut LeanObject,
    mut v_matcher_2202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    v___x_2203_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2201_, v_matcher_2202_);
    return v___x_2203_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(
    mut v_motive_2204_: *mut LeanObject,
    mut v_t_2205_: *mut LeanObject,
    mut v_h_2206_: *mut LeanObject,
    mut v_matcher_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    v___x_2208_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_2205_, v_matcher_2207_);
    return v___x_2208_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2()
-> *mut LeanObject {
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    v___x_2212_ = lean_box(0);
    v___x_2213_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1;
    v___x_2214_ = l_Lean_Expr_const___override(v___x_2213_, v___x_2212_);
    return v___x_2214_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3()
-> *mut LeanObject {
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    v___x_2215_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2,
    );
    v___x_2216_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2216_, 0, v___x_2215_);
    return v___x_2216_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default() -> *mut LeanObject {
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    v___x_2217_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3,
    );
    return v___x_2217_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo() -> *mut LeanObject {
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    v___x_2218_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
    return v___x_2218_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(
    mut v_x_2219_: *mut LeanObject,
    mut v_x_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2222_: u8 = 0;
    let mut v_one_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2228_: u8 = 0;
    let mut v_body_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2221_ = lean_unsigned_to_nat(0);
                v_isZero_2222_ = lean_nat_dec_eq(v_x_2219_, v_zero_2221_);
                if v_isZero_2222_ == 1 {
                    lean_dec(v_x_2219_);
                    return v_x_2220_;
                } else {
                    v_one_2223_ = lean_unsigned_to_nat(1);
                    v_n_2224_ = lean_nat_sub(v_x_2219_, v_one_2223_);
                    lean_dec(v_x_2219_);
                    if lean_obj_tag(v_x_2220_) == 1 {
                        v_val_2225_ = lean_ctor_get(v_x_2220_, 0);
                        v_isSharedCheck_2236_ = (!lean_is_exclusive(v_x_2220_)) as u8;
                        if v_isSharedCheck_2236_ == 0 {
                            v___x_2227_ = v_x_2220_;
                            v_isShared_2228_ = v_isSharedCheck_2236_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2225_);
                            lean_dec(v_x_2220_);
                            v___x_2227_ = lean_box(0);
                            v_isShared_2228_ = v_isSharedCheck_2236_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_x_2220_);
                        v___x_2237_ = lean_box(0);
                        v_x_2219_ = v_n_2224_;
                        v_x_2220_ = v___x_2237_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_val_2225_) == 6 {
                    v_body_2229_ = lean_ctor_get(v_val_2225_, 2);
                    lean_inc_ref(v_body_2229_);
                    lean_dec_ref_known(v_val_2225_, 3);
                    if v_isShared_2228_ == 0 {
                        lean_ctor_set(v___x_2227_, 0, v_body_2229_);
                        v___x_2231_ = v___x_2227_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_body_2229_);
                        v___x_2231_ = v_reuseFailAlloc_2233_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2227_);
                    lean_dec(v_val_2225_);
                    v___x_2234_ = lean_box(0);
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
    mut v_info_2239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherApp_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v_toMatcherInfo_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v_e_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_2239_) == 2 {
                    v_matcherApp_2247_ = lean_ctor_get(v_info_2239_, 0);
                    v_isSharedCheck_2264_ = (!lean_is_exclusive(v_info_2239_)) as u8;
                    if v_isSharedCheck_2264_ == 0 {
                        v___x_2249_ = v_info_2239_;
                        v_isShared_2250_ = v_isSharedCheck_2264_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_matcherApp_2247_);
                        lean_dec(v_info_2239_);
                        v___x_2249_ = lean_box(0);
                        v_isShared_2250_ = v_isSharedCheck_2264_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_e_2265_ = lean_ctor_get(v_info_2239_, 0);
                    lean_inc_ref(v_e_2265_);
                    lean_dec_ref(v_info_2239_);
                    v_e_2241_ = v_e_2265_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2242_ = l_Lean_Expr_getAppNumArgs(v_e_2241_);
                v___x_2243_ = lean_unsigned_to_nat(1);
                v___x_2244_ = lean_nat_sub(v___x_2242_, v___x_2243_);
                lean_dec(v___x_2242_);
                v___x_2245_ = l_Lean_Expr_getRevArg_x21(v_e_2241_, v___x_2244_);
                lean_dec_ref(v_e_2241_);
                v___x_2246_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2246_, 0, v___x_2245_);
                return v___x_2246_;
            }
            2 => {
                v_toMatcherInfo_2251_ = lean_ctor_get(v_matcherApp_2247_, 0);
                lean_inc_ref(v_toMatcherInfo_2251_);
                v_motive_2252_ = lean_ctor_get(v_matcherApp_2247_, 4);
                lean_inc_ref_n(v_motive_2252_, 2);
                lean_dec_ref(v_matcherApp_2247_);
                v_discrInfos_2253_ = lean_ctor_get(v_toMatcherInfo_2251_, 4);
                lean_inc_ref(v_discrInfos_2253_);
                lean_dec_ref(v_toMatcherInfo_2251_);
                v___x_2254_ = lean_array_get_size(v_discrInfos_2253_);
                lean_dec_ref(v_discrInfos_2253_);
                if v_isShared_2250_ == 0 {
                    lean_ctor_set_tag(v___x_2249_, 1);
                    lean_ctor_set(v___x_2249_, 0, v_motive_2252_);
                    v___x_2256_ = v___x_2249_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_motive_2252_);
                    v___x_2256_ = v_reuseFailAlloc_2263_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2257_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(v___x_2254_, v___x_2256_);
                if lean_obj_tag(v___x_2257_) == 0 {
                    lean_dec_ref(v_motive_2252_);
                    return v___x_2257_;
                } else {
                    v_val_2258_ = lean_ctor_get(v___x_2257_, 0);
                    lean_inc(v_val_2258_);
                    v___x_2259_ = l_Lean_Expr_looseBVarRange(v_val_2258_);
                    lean_dec(v_val_2258_);
                    v___x_2260_ = l_Lean_Expr_looseBVarRange(v_motive_2252_);
                    lean_dec_ref(v_motive_2252_);
                    v___x_2261_ = lean_nat_dec_eq(v___x_2259_, v___x_2260_);
                    lean_dec(v___x_2260_);
                    lean_dec(v___x_2259_);
                    if v___x_2261_ == 0 {
                        lean_dec_ref_known(v___x_2257_, 1);
                        v___x_2262_ = lean_box(0);
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
    mut v_matcherApp_2266_: *mut LeanObject,
    mut v_as_2267_: *mut LeanObject,
    mut v_i_2268_: *mut LeanObject,
    mut v_j_2269_: *mut LeanObject,
    mut v_bs_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2272_: u8 = 0;
    let mut v_alts_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2271_ = lean_unsigned_to_nat(0);
                v_isZero_2272_ = lean_nat_dec_eq(v_i_2268_, v_zero_2271_);
                if v_isZero_2272_ == 1 {
                    lean_dec(v_j_2269_);
                    lean_dec(v_i_2268_);
                    return v_bs_2270_;
                } else {
                    v_alts_2273_ = lean_ctor_get(v_matcherApp_2266_, 6);
                    v___x_2274_ = l_Lean_instInhabitedExpr;
                    v_one_2275_ = lean_unsigned_to_nat(1);
                    v_n_2276_ = lean_nat_sub(v_i_2268_, v_one_2275_);
                    lean_dec(v_i_2268_);
                    v___x_2277_ = lean_array_fget_borrowed(v_as_2267_, v_j_2269_);
                    v___x_2278_ = lean_array_get_borrowed(v___x_2274_, v_alts_2273_, v_j_2269_);
                    lean_inc(v___x_2278_);
                    lean_inc(v___x_2277_);
                    v___x_2279_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2279_, 0, v___x_2277_);
                    lean_ctor_set(v___x_2279_, 1, v___x_2278_);
                    v___x_2280_ = lean_nat_add(v_j_2269_, v_one_2275_);
                    lean_dec(v_j_2269_);
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
    mut v_matcherApp_2283_: *mut LeanObject,
    mut v_as_2284_: *mut LeanObject,
    mut v_i_2285_: *mut LeanObject,
    mut v_j_2286_: *mut LeanObject,
    mut v_bs_2287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2288_: *mut LeanObject = core::ptr::null_mut();
    v_res_2288_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(
            v_matcherApp_2283_,
            v_as_2284_,
            v_i_2285_,
            v_j_2286_,
            v_bs_2287_,
        );
    lean_dec_ref(v_as_2284_);
    lean_dec_ref(v_matcherApp_2283_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(
    mut v_info_2289_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_info_2289_) {
        0 => {
            let mut v_e_2290_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
            v_e_2290_ = lean_ctor_get(v_info_2289_, 0);
            lean_inc_ref(v_e_2290_);
            lean_dec_ref_known(v_info_2289_, 1);
            v___x_2291_ = lean_unsigned_to_nat(0);
            v___x_2292_ = lean_unsigned_to_nat(3);
            v___x_2293_ = l_Lean_Expr_getAppNumArgs(v_e_2290_);
            v___x_2294_ = lean_nat_sub(v___x_2293_, v___x_2292_);
            v___x_2295_ = lean_unsigned_to_nat(1);
            v___x_2296_ = lean_nat_sub(v___x_2294_, v___x_2295_);
            lean_dec(v___x_2294_);
            v___x_2297_ = l_Lean_Expr_getRevArg_x21(v_e_2290_, v___x_2296_);
            v___x_2298_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2298_, 0, v___x_2291_);
            lean_ctor_set(v___x_2298_, 1, v___x_2297_);
            v___x_2299_ = lean_unsigned_to_nat(4);
            v___x_2300_ = lean_nat_sub(v___x_2293_, v___x_2299_);
            lean_dec(v___x_2293_);
            v___x_2301_ = lean_nat_sub(v___x_2300_, v___x_2295_);
            lean_dec(v___x_2300_);
            v___x_2302_ = l_Lean_Expr_getRevArg_x21(v_e_2290_, v___x_2301_);
            lean_dec_ref(v_e_2290_);
            v___x_2303_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2303_, 0, v___x_2291_);
            lean_ctor_set(v___x_2303_, 1, v___x_2302_);
            v___x_2304_ = lean_unsigned_to_nat(2);
            v___x_2305_ = lean_mk_empty_array_with_capacity(v___x_2304_);
            v___x_2306_ = lean_array_push(v___x_2305_, v___x_2298_);
            v___x_2307_ = lean_array_push(v___x_2306_, v___x_2303_);
            return v___x_2307_;
        }
        1 => {
            let mut v_e_2308_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
            v_e_2308_ = lean_ctor_get(v_info_2289_, 0);
            lean_inc_ref(v_e_2308_);
            lean_dec_ref_known(v_info_2289_, 1);
            v___x_2309_ = lean_unsigned_to_nat(1);
            v___x_2310_ = lean_unsigned_to_nat(3);
            v___x_2311_ = l_Lean_Expr_getAppNumArgs(v_e_2308_);
            v___x_2312_ = lean_nat_sub(v___x_2311_, v___x_2310_);
            v___x_2313_ = lean_nat_sub(v___x_2312_, v___x_2309_);
            lean_dec(v___x_2312_);
            v___x_2314_ = l_Lean_Expr_getRevArg_x21(v_e_2308_, v___x_2313_);
            v___x_2315_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2315_, 0, v___x_2309_);
            lean_ctor_set(v___x_2315_, 1, v___x_2314_);
            v___x_2316_ = lean_unsigned_to_nat(4);
            v___x_2317_ = lean_nat_sub(v___x_2311_, v___x_2316_);
            lean_dec(v___x_2311_);
            v___x_2318_ = lean_nat_sub(v___x_2317_, v___x_2309_);
            lean_dec(v___x_2317_);
            v___x_2319_ = l_Lean_Expr_getRevArg_x21(v_e_2308_, v___x_2318_);
            lean_dec_ref(v_e_2308_);
            v___x_2320_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2320_, 0, v___x_2309_);
            lean_ctor_set(v___x_2320_, 1, v___x_2319_);
            v___x_2321_ = lean_unsigned_to_nat(2);
            v___x_2322_ = lean_mk_empty_array_with_capacity(v___x_2321_);
            v___x_2323_ = lean_array_push(v___x_2322_, v___x_2315_);
            v___x_2324_ = lean_array_push(v___x_2323_, v___x_2320_);
            return v___x_2324_;
        }
        _ => {
            let mut v_matcherApp_2325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
            v_matcherApp_2325_ = lean_ctor_get(v_info_2289_, 0);
            lean_inc_ref_n(v_matcherApp_2325_, 2);
            lean_dec_ref_known(v_info_2289_, 1);
            v___x_2326_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2325_);
            v___x_2327_ = lean_array_get_size(v___x_2326_);
            v___x_2328_ = lean_unsigned_to_nat(0);
            v___x_2329_ = lean_mk_empty_array_with_capacity(v___x_2327_);
            v___x_2330_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_2325_, v___x_2326_, v___x_2327_, v___x_2328_, v___x_2329_);
            lean_dec_ref(v___x_2326_);
            lean_dec_ref(v_matcherApp_2325_);
            return v___x_2330_;
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(
    mut v_matcherApp_2331_: *mut LeanObject,
    mut v_as_2332_: *mut LeanObject,
    mut v_i_2333_: *mut LeanObject,
    mut v_j_2334_: *mut LeanObject,
    mut v_inv_2335_: *mut LeanObject,
    mut v_bs_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_matcherApp_2338_: *mut LeanObject,
    mut v_as_2339_: *mut LeanObject,
    mut v_i_2340_: *mut LeanObject,
    mut v_j_2341_: *mut LeanObject,
    mut v_inv_2342_: *mut LeanObject,
    mut v_bs_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2344_: *mut LeanObject = core::ptr::null_mut();
    v_res_2344_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(
        v_matcherApp_2338_,
        v_as_2339_,
        v_i_2340_,
        v_j_2341_,
        v_inv_2342_,
        v_bs_2343_,
    );
    lean_dec_ref(v_as_2339_);
    lean_dec_ref(v_matcherApp_2338_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_expr(
    mut v_x_2345_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2345_) == 2 {
        let mut v_matcherApp_2346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
        v_matcherApp_2346_ = lean_ctor_get(v_x_2345_, 0);
        lean_inc_ref(v_matcherApp_2346_);
        lean_dec_ref_known(v_x_2345_, 1);
        v___x_2347_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_2346_);
        return v___x_2347_;
    } else {
        let mut v_e_2348_: *mut LeanObject = core::ptr::null_mut();
        v_e_2348_ = lean_ctor_get(v_x_2345_, 0);
        lean_inc_ref(v_e_2348_);
        lean_dec_ref(v_x_2345_);
        return v_e_2348_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(
    mut v___x_2352_: *mut LeanObject,
    mut v_resTy_2353_: *mut LeanObject,
    mut v_c_2354_: *mut LeanObject,
    mut v_dec_2355_: *mut LeanObject,
    mut v_t_2356_: *mut LeanObject,
    mut v_e_2357_: *mut LeanObject,
    mut v_k_2358_: *mut LeanObject,
    mut v_u_2359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    v___x_2360_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1;
    v___x_2361_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2361_, 0, v_u_2359_);
    lean_ctor_set(v___x_2361_, 1, v___x_2352_);
    v___x_2362_ = l_Lean_mkConst(v___x_2360_, v___x_2361_);
    lean_inc_ref(v_e_2357_);
    lean_inc_ref(v_t_2356_);
    lean_inc_ref(v_dec_2355_);
    lean_inc_ref(v_c_2354_);
    v___x_2363_ = l_Lean_mkApp5(
        v___x_2362_,
        v_resTy_2353_,
        v_c_2354_,
        v_dec_2355_,
        v_t_2356_,
        v_e_2357_,
    );
    v___x_2364_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2364_, 0, v___x_2363_);
    v___x_2365_ = lean_unsigned_to_nat(4);
    v___x_2366_ = lean_mk_empty_array_with_capacity(v___x_2365_);
    v___x_2367_ = lean_array_push(v___x_2366_, v_c_2354_);
    v___x_2368_ = lean_array_push(v___x_2367_, v_dec_2355_);
    v___x_2369_ = lean_array_push(v___x_2368_, v_t_2356_);
    v___x_2370_ = lean_array_push(v___x_2369_, v_e_2357_);
    v___x_2371_ = lean_apply_2(v_k_2358_, v___x_2364_, v___x_2370_);
    return v___x_2371_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(
    mut v___x_2372_: *mut LeanObject,
    mut v_resTy_2373_: *mut LeanObject,
    mut v_c_2374_: *mut LeanObject,
    mut v_dec_2375_: *mut LeanObject,
    mut v_t_2376_: *mut LeanObject,
    mut v_k_2377_: *mut LeanObject,
    mut v_inst_2378_: *mut LeanObject,
    mut v_toBind_2379_: *mut LeanObject,
    mut v_e_2380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_resTy_2373_);
    v___f_2381_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2381_, 0, v___x_2372_);
    lean_closure_set(v___f_2381_, 1, v_resTy_2373_);
    lean_closure_set(v___f_2381_, 2, v_c_2374_);
    lean_closure_set(v___f_2381_, 3, v_dec_2375_);
    lean_closure_set(v___f_2381_, 4, v_t_2376_);
    lean_closure_set(v___f_2381_, 5, v_e_2380_);
    lean_closure_set(v___f_2381_, 6, v_k_2377_);
    v___x_2382_ = lean_alloc_closure(l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void, 6, 1);
    lean_closure_set(v___x_2382_, 0, v_resTy_2373_);
    v___x_2383_ = lean_apply_2(v_inst_2378_, lean_box(0), v___x_2382_);
    v___x_2384_ = lean_apply_4(
        v_toBind_2379_,
        lean_box(0),
        lean_box(0),
        v___x_2383_,
        v___f_2381_,
    );
    return v___x_2384_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(
    mut v___x_2388_: *mut LeanObject,
    mut v_resTy_2389_: *mut LeanObject,
    mut v_c_2390_: *mut LeanObject,
    mut v_dec_2391_: *mut LeanObject,
    mut v_k_2392_: *mut LeanObject,
    mut v_inst_2393_: *mut LeanObject,
    mut v_toBind_2394_: *mut LeanObject,
    mut v_inst_2395_: *mut LeanObject,
    mut v_inst_2396_: *mut LeanObject,
    mut v_t_2397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_resTy_2389_);
    v___f_2398_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_2398_, 0, v___x_2388_);
    lean_closure_set(v___f_2398_, 1, v_resTy_2389_);
    lean_closure_set(v___f_2398_, 2, v_c_2390_);
    lean_closure_set(v___f_2398_, 3, v_dec_2391_);
    lean_closure_set(v___f_2398_, 4, v_t_2397_);
    lean_closure_set(v___f_2398_, 5, v_k_2392_);
    lean_closure_set(v___f_2398_, 6, v_inst_2393_);
    lean_closure_set(v___f_2398_, 7, v_toBind_2394_);
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
    mut v___x_2404_: *mut LeanObject,
    mut v_resTy_2405_: *mut LeanObject,
    mut v_c_2406_: *mut LeanObject,
    mut v_k_2407_: *mut LeanObject,
    mut v_inst_2408_: *mut LeanObject,
    mut v_toBind_2409_: *mut LeanObject,
    mut v_inst_2410_: *mut LeanObject,
    mut v_inst_2411_: *mut LeanObject,
    mut v_dec_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2411_);
    lean_inc_ref(v_inst_2410_);
    lean_inc_ref(v_resTy_2405_);
    v___f_2413_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_2413_, 0, v___x_2404_);
    lean_closure_set(v___f_2413_, 1, v_resTy_2405_);
    lean_closure_set(v___f_2413_, 2, v_c_2406_);
    lean_closure_set(v___f_2413_, 3, v_dec_2412_);
    lean_closure_set(v___f_2413_, 4, v_k_2407_);
    lean_closure_set(v___f_2413_, 5, v_inst_2408_);
    lean_closure_set(v___f_2413_, 6, v_toBind_2409_);
    lean_closure_set(v___f_2413_, 7, v_inst_2410_);
    lean_closure_set(v___f_2413_, 8, v_inst_2411_);
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
-> *mut LeanObject {
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    v___x_2422_ = lean_box(0);
    v___x_2423_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3;
    v___x_2424_ = l_Lean_mkConst(v___x_2423_, v___x_2422_);
    return v___x_2424_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(
    mut v_resTy_2425_: *mut LeanObject,
    mut v_k_2426_: *mut LeanObject,
    mut v_inst_2427_: *mut LeanObject,
    mut v_toBind_2428_: *mut LeanObject,
    mut v_inst_2429_: *mut LeanObject,
    mut v_inst_2430_: *mut LeanObject,
    mut v_c_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    v___x_2432_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1;
    v___x_2433_ = lean_box(0);
    lean_inc_ref(v_inst_2430_);
    lean_inc_ref(v_inst_2429_);
    lean_inc_ref(v_c_2431_);
    v___f_2434_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_2434_, 0, v___x_2433_);
    lean_closure_set(v___f_2434_, 1, v_resTy_2425_);
    lean_closure_set(v___f_2434_, 2, v_c_2431_);
    lean_closure_set(v___f_2434_, 3, v_k_2426_);
    lean_closure_set(v___f_2434_, 4, v_inst_2427_);
    lean_closure_set(v___f_2434_, 5, v_toBind_2428_);
    lean_closure_set(v___f_2434_, 6, v_inst_2429_);
    lean_closure_set(v___f_2434_, 7, v_inst_2430_);
    v___x_2435_ = lean_obj_once(
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
    mut v_c_2438_: *mut LeanObject,
    mut v_resTy_2439_: *mut LeanObject,
    mut v___y_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    v___x_2445_ = l_Lean_mkArrow(v_c_2438_, v_resTy_2439_, v___y_2442_, v___y_2443_);
    return v___x_2445_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(
    mut v_c_2446_: *mut LeanObject,
    mut v_resTy_2447_: *mut LeanObject,
    mut v___y_2448_: *mut LeanObject,
    mut v___y_2449_: *mut LeanObject,
    mut v___y_2450_: *mut LeanObject,
    mut v___y_2451_: *mut LeanObject,
    mut v___y_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2453_: *mut LeanObject = core::ptr::null_mut();
    v_res_2453_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(
        v_c_2446_,
        v_resTy_2447_,
        v___y_2448_,
        v___y_2449_,
        v___y_2450_,
        v___y_2451_,
    );
    lean_dec(v___y_2451_);
    lean_dec_ref(v___y_2450_);
    lean_dec(v___y_2449_);
    lean_dec_ref(v___y_2448_);
    return v_res_2453_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(
    mut v___x_2457_: *mut LeanObject,
    mut v_resTy_2458_: *mut LeanObject,
    mut v_c_2459_: *mut LeanObject,
    mut v_dec_2460_: *mut LeanObject,
    mut v_t_2461_: *mut LeanObject,
    mut v_e_2462_: *mut LeanObject,
    mut v_k_2463_: *mut LeanObject,
    mut v_u_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2465_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1;
    v___x_2466_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2466_, 0, v_u_2464_);
    lean_ctor_set(v___x_2466_, 1, v___x_2457_);
    v___x_2467_ = l_Lean_mkConst(v___x_2465_, v___x_2466_);
    lean_inc_ref(v_e_2462_);
    lean_inc_ref(v_t_2461_);
    lean_inc_ref(v_dec_2460_);
    lean_inc_ref(v_c_2459_);
    v___x_2468_ = l_Lean_mkApp5(
        v___x_2467_,
        v_resTy_2458_,
        v_c_2459_,
        v_dec_2460_,
        v_t_2461_,
        v_e_2462_,
    );
    v___x_2469_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2469_, 0, v___x_2468_);
    v___x_2470_ = lean_unsigned_to_nat(4);
    v___x_2471_ = lean_mk_empty_array_with_capacity(v___x_2470_);
    v___x_2472_ = lean_array_push(v___x_2471_, v_c_2459_);
    v___x_2473_ = lean_array_push(v___x_2472_, v_dec_2460_);
    v___x_2474_ = lean_array_push(v___x_2473_, v_t_2461_);
    v___x_2475_ = lean_array_push(v___x_2474_, v_e_2462_);
    v___x_2476_ = lean_apply_2(v_k_2463_, v___x_2469_, v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(
    mut v___x_2477_: *mut LeanObject,
    mut v_resTy_2478_: *mut LeanObject,
    mut v_c_2479_: *mut LeanObject,
    mut v_dec_2480_: *mut LeanObject,
    mut v_t_2481_: *mut LeanObject,
    mut v_k_2482_: *mut LeanObject,
    mut v_inst_2483_: *mut LeanObject,
    mut v_toBind_2484_: *mut LeanObject,
    mut v_e_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_resTy_2478_);
    v___f_2486_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2486_, 0, v___x_2477_);
    lean_closure_set(v___f_2486_, 1, v_resTy_2478_);
    lean_closure_set(v___f_2486_, 2, v_c_2479_);
    lean_closure_set(v___f_2486_, 3, v_dec_2480_);
    lean_closure_set(v___f_2486_, 4, v_t_2481_);
    lean_closure_set(v___f_2486_, 5, v_e_2485_);
    lean_closure_set(v___f_2486_, 6, v_k_2482_);
    v___x_2487_ = lean_alloc_closure(l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void, 6, 1);
    lean_closure_set(v___x_2487_, 0, v_resTy_2478_);
    v___x_2488_ = lean_apply_2(v_inst_2483_, lean_box(0), v___x_2487_);
    v___x_2489_ = lean_apply_4(
        v_toBind_2484_,
        lean_box(0),
        lean_box(0),
        v___x_2488_,
        v___f_2486_,
    );
    return v___x_2489_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(
    mut v___x_2490_: *mut LeanObject,
    mut v_resTy_2491_: *mut LeanObject,
    mut v_c_2492_: *mut LeanObject,
    mut v_dec_2493_: *mut LeanObject,
    mut v_k_2494_: *mut LeanObject,
    mut v_inst_2495_: *mut LeanObject,
    mut v_toBind_2496_: *mut LeanObject,
    mut v_inst_2497_: *mut LeanObject,
    mut v_inst_2498_: *mut LeanObject,
    mut v_eTy_2499_: *mut LeanObject,
    mut v_t_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    v___f_2501_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7 as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_2501_, 0, v___x_2490_);
    lean_closure_set(v___f_2501_, 1, v_resTy_2491_);
    lean_closure_set(v___f_2501_, 2, v_c_2492_);
    lean_closure_set(v___f_2501_, 3, v_dec_2493_);
    lean_closure_set(v___f_2501_, 4, v_t_2500_);
    lean_closure_set(v___f_2501_, 5, v_k_2494_);
    lean_closure_set(v___f_2501_, 6, v_inst_2495_);
    lean_closure_set(v___f_2501_, 7, v_toBind_2496_);
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
    mut v___x_2504_: *mut LeanObject,
    mut v_resTy_2505_: *mut LeanObject,
    mut v_c_2506_: *mut LeanObject,
    mut v_dec_2507_: *mut LeanObject,
    mut v_k_2508_: *mut LeanObject,
    mut v_inst_2509_: *mut LeanObject,
    mut v_toBind_2510_: *mut LeanObject,
    mut v_inst_2511_: *mut LeanObject,
    mut v_inst_2512_: *mut LeanObject,
    mut v_tTy_2513_: *mut LeanObject,
    mut v_eTy_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_2512_);
    lean_inc_ref(v_inst_2511_);
    v___f_2515_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8 as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_2515_, 0, v___x_2504_);
    lean_closure_set(v___f_2515_, 1, v_resTy_2505_);
    lean_closure_set(v___f_2515_, 2, v_c_2506_);
    lean_closure_set(v___f_2515_, 3, v_dec_2507_);
    lean_closure_set(v___f_2515_, 4, v_k_2508_);
    lean_closure_set(v___f_2515_, 5, v_inst_2509_);
    lean_closure_set(v___f_2515_, 6, v_toBind_2510_);
    lean_closure_set(v___f_2515_, 7, v_inst_2511_);
    lean_closure_set(v___f_2515_, 8, v_inst_2512_);
    lean_closure_set(v___f_2515_, 9, v_eTy_2514_);
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
    mut v___x_2518_: *mut LeanObject,
    mut v_resTy_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    v___x_2525_ = l_Lean_mkArrow(v___x_2518_, v_resTy_2519_, v___y_2522_, v___y_2523_);
    return v___x_2525_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(
    mut v___x_2526_: *mut LeanObject,
    mut v_resTy_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2533_: *mut LeanObject = core::ptr::null_mut();
    v_res_2533_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(
        v___x_2526_,
        v_resTy_2527_,
        v___y_2528_,
        v___y_2529_,
        v___y_2530_,
        v___y_2531_,
    );
    lean_dec(v___y_2531_);
    lean_dec_ref(v___y_2530_);
    lean_dec(v___y_2529_);
    lean_dec_ref(v___y_2528_);
    return v_res_2533_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(
    mut v___x_2534_: *mut LeanObject,
    mut v_resTy_2535_: *mut LeanObject,
    mut v_c_2536_: *mut LeanObject,
    mut v_dec_2537_: *mut LeanObject,
    mut v_k_2538_: *mut LeanObject,
    mut v_inst_2539_: *mut LeanObject,
    mut v_toBind_2540_: *mut LeanObject,
    mut v_inst_2541_: *mut LeanObject,
    mut v_inst_2542_: *mut LeanObject,
    mut v_tTy_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_2540_);
    lean_inc(v_inst_2539_);
    lean_inc_ref(v_c_2536_);
    lean_inc_ref(v_resTy_2535_);
    v___f_2544_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9 as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_2544_, 0, v___x_2534_);
    lean_closure_set(v___f_2544_, 1, v_resTy_2535_);
    lean_closure_set(v___f_2544_, 2, v_c_2536_);
    lean_closure_set(v___f_2544_, 3, v_dec_2537_);
    lean_closure_set(v___f_2544_, 4, v_k_2538_);
    lean_closure_set(v___f_2544_, 5, v_inst_2539_);
    lean_closure_set(v___f_2544_, 6, v_toBind_2540_);
    lean_closure_set(v___f_2544_, 7, v_inst_2541_);
    lean_closure_set(v___f_2544_, 8, v_inst_2542_);
    lean_closure_set(v___f_2544_, 9, v_tTy_2543_);
    v___x_2545_ = l_Lean_mkNot(v_c_2536_);
    v___f_2546_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_2546_, 0, v___x_2545_);
    lean_closure_set(v___f_2546_, 1, v_resTy_2535_);
    v___x_2547_ = lean_apply_2(v_inst_2539_, lean_box(0), v___f_2546_);
    v___x_2548_ = lean_apply_4(
        v_toBind_2540_,
        lean_box(0),
        lean_box(0),
        v___x_2547_,
        v___f_2544_,
    );
    return v___x_2548_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(
    mut v___x_2549_: *mut LeanObject,
    mut v_resTy_2550_: *mut LeanObject,
    mut v_c_2551_: *mut LeanObject,
    mut v_k_2552_: *mut LeanObject,
    mut v_inst_2553_: *mut LeanObject,
    mut v_toBind_2554_: *mut LeanObject,
    mut v_inst_2555_: *mut LeanObject,
    mut v_inst_2556_: *mut LeanObject,
    mut v___f_2557_: *mut LeanObject,
    mut v_dec_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_2554_);
    lean_inc(v_inst_2553_);
    v___f_2559_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_2559_, 0, v___x_2549_);
    lean_closure_set(v___f_2559_, 1, v_resTy_2550_);
    lean_closure_set(v___f_2559_, 2, v_c_2551_);
    lean_closure_set(v___f_2559_, 3, v_dec_2558_);
    lean_closure_set(v___f_2559_, 4, v_k_2552_);
    lean_closure_set(v___f_2559_, 5, v_inst_2553_);
    lean_closure_set(v___f_2559_, 6, v_toBind_2554_);
    lean_closure_set(v___f_2559_, 7, v_inst_2555_);
    lean_closure_set(v___f_2559_, 8, v_inst_2556_);
    v___x_2560_ = lean_apply_2(v_inst_2553_, lean_box(0), v___f_2557_);
    v___x_2561_ = lean_apply_4(
        v_toBind_2554_,
        lean_box(0),
        lean_box(0),
        v___x_2560_,
        v___f_2559_,
    );
    return v___x_2561_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(
    mut v_resTy_2562_: *mut LeanObject,
    mut v_k_2563_: *mut LeanObject,
    mut v_inst_2564_: *mut LeanObject,
    mut v_toBind_2565_: *mut LeanObject,
    mut v_inst_2566_: *mut LeanObject,
    mut v_inst_2567_: *mut LeanObject,
    mut v_c_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_resTy_2562_);
    lean_inc_ref_n(v_c_2568_, 2);
    v___f_2569_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_2569_, 0, v_c_2568_);
    lean_closure_set(v___f_2569_, 1, v_resTy_2562_);
    v___x_2570_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1;
    v___x_2571_ = lean_box(0);
    lean_inc_ref(v_inst_2567_);
    lean_inc_ref(v_inst_2566_);
    v___f_2572_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12 as *mut core::ffi::c_void,
        10,
        9,
    );
    lean_closure_set(v___f_2572_, 0, v___x_2571_);
    lean_closure_set(v___f_2572_, 1, v_resTy_2562_);
    lean_closure_set(v___f_2572_, 2, v_c_2568_);
    lean_closure_set(v___f_2572_, 3, v_k_2563_);
    lean_closure_set(v___f_2572_, 4, v_inst_2564_);
    lean_closure_set(v___f_2572_, 5, v_toBind_2565_);
    lean_closure_set(v___f_2572_, 6, v_inst_2566_);
    lean_closure_set(v___f_2572_, 7, v_inst_2567_);
    lean_closure_set(v___f_2572_, 8, v___f_2569_);
    v___x_2573_ = lean_obj_once(
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
    mut v_resTy_2576_: *mut LeanObject,
    mut v_motiveArgs_2577_: *mut LeanObject,
    mut v_x_2578_: *mut LeanObject,
    mut v___y_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
    mut v___y_2581_: *mut LeanObject,
    mut v___y_2582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2584_: u8 = 0;
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_resTy_2588_: *mut LeanObject,
    mut v_motiveArgs_2589_: *mut LeanObject,
    mut v_x_2590_: *mut LeanObject,
    mut v___y_2591_: *mut LeanObject,
    mut v___y_2592_: *mut LeanObject,
    mut v___y_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
    mut v___y_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2596_: *mut LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(
        v_resTy_2588_,
        v_motiveArgs_2589_,
        v_x_2590_,
        v___y_2591_,
        v___y_2592_,
        v___y_2593_,
        v___y_2594_,
    );
    lean_dec(v___y_2594_);
    lean_dec_ref(v___y_2593_);
    lean_dec(v___y_2592_);
    lean_dec_ref(v___y_2591_);
    lean_dec_ref(v_x_2590_);
    lean_dec_ref(v_motiveArgs_2589_);
    return v_res_2596_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(
    mut v_i_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
    mut v_x_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    v___x_2603_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___closed__1;
    v___x_2604_ = lean_unsigned_to_nat(1);
    v___x_2605_ = lean_nat_add(v_i_2600_, v___x_2604_);
    v___x_2606_ = lean_name_append_index_after(v___x_2603_, v___x_2605_);
    v___x_2607_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2607_, 0, v___x_2606_);
    lean_ctor_set(v___x_2607_, 1, v_a_2601_);
    return v___x_2607_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(
    mut v_i_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_x_2610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2611_: *mut LeanObject = core::ptr::null_mut();
    v_res_2611_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(
        v_i_2608_, v_a_2609_, v_x_2610_,
    );
    lean_dec(v_i_2608_);
    return v_res_2611_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(
    mut v_i_2615_: *mut LeanObject,
    mut v_toPure_2616_: *mut LeanObject,
    mut v_____do__lift_2617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    v___x_2618_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___closed__1;
    v___x_2619_ = lean_unsigned_to_nat(1);
    v___x_2620_ = lean_nat_add(v_i_2615_, v___x_2619_);
    v___x_2621_ = lean_name_append_index_after(v___x_2618_, v___x_2620_);
    v___x_2622_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2622_, 0, v___x_2621_);
    lean_ctor_set(v___x_2622_, 1, v_____do__lift_2617_);
    v___x_2623_ = lean_apply_2(v_toPure_2616_, lean_box(0), v___x_2622_);
    return v___x_2623_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(
    mut v_i_2624_: *mut LeanObject,
    mut v_toPure_2625_: *mut LeanObject,
    mut v_____do__lift_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2627_: *mut LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(
        v_i_2624_,
        v_toPure_2625_,
        v_____do__lift_2626_,
    );
    lean_dec(v_i_2624_);
    return v_res_2627_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(
    mut v_toPure_2628_: *mut LeanObject,
    mut v_inst_2629_: *mut LeanObject,
    mut v_toBind_2630_: *mut LeanObject,
    mut v_i_2631_: *mut LeanObject,
    mut v_a_2632_: *mut LeanObject,
    mut v_x_2633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    v___f_2634_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2634_, 0, v_i_2631_);
    lean_closure_set(v___f_2634_, 1, v_toPure_2628_);
    v___x_2635_ = lean_alloc_closure(
        l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_2635_, 0, v_a_2632_);
    v___x_2636_ = lean_apply_2(v_inst_2629_, lean_box(0), v___x_2635_);
    v___x_2637_ = lean_apply_4(
        v_toBind_2630_,
        lean_box(0),
        lean_box(0),
        v___x_2636_,
        v___f_2634_,
    );
    return v___x_2637_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(
    mut v_toMatcherInfo_2640_: *mut LeanObject,
    mut v_matcherName_2641_: *mut LeanObject,
    mut v_matcherLevels_2642_: *mut LeanObject,
    mut v_params_2643_: *mut LeanObject,
    mut v_motive_2644_: *mut LeanObject,
    mut v_discrs_2645_: *mut LeanObject,
    mut v_alts_2646_: *mut LeanObject,
    mut v_k_2647_: *mut LeanObject,
    mut v_____do__lift_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abstractMatcherApp_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    v___x_2649_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    lean_inc_ref(v_discrs_2645_);
    v_abstractMatcherApp_2650_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v_abstractMatcherApp_2650_, 0, v_toMatcherInfo_2640_);
    lean_ctor_set(v_abstractMatcherApp_2650_, 1, v_matcherName_2641_);
    lean_ctor_set(v_abstractMatcherApp_2650_, 2, v_matcherLevels_2642_);
    lean_ctor_set(v_abstractMatcherApp_2650_, 3, v_params_2643_);
    lean_ctor_set(v_abstractMatcherApp_2650_, 4, v_motive_2644_);
    lean_ctor_set(v_abstractMatcherApp_2650_, 5, v_discrs_2645_);
    lean_ctor_set(v_abstractMatcherApp_2650_, 6, v_____do__lift_2648_);
    lean_ctor_set(v_abstractMatcherApp_2650_, 7, v___x_2649_);
    v___x_2651_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2651_, 0, v_abstractMatcherApp_2650_);
    v___x_2652_ = l_Array_append___redArg(v_discrs_2645_, v_alts_2646_);
    v___x_2653_ = lean_apply_2(v_k_2647_, v___x_2651_, v___x_2652_);
    return v___x_2653_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(
    mut v_toMatcherInfo_2654_: *mut LeanObject,
    mut v_matcherName_2655_: *mut LeanObject,
    mut v_matcherLevels_2656_: *mut LeanObject,
    mut v_params_2657_: *mut LeanObject,
    mut v_motive_2658_: *mut LeanObject,
    mut v_discrs_2659_: *mut LeanObject,
    mut v_alts_2660_: *mut LeanObject,
    mut v_k_2661_: *mut LeanObject,
    mut v_____do__lift_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2663_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_alts_2660_);
    return v_res_2663_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(
    mut v_toMatcherInfo_2665_: *mut LeanObject,
    mut v_matcherName_2666_: *mut LeanObject,
    mut v_matcherLevels_2667_: *mut LeanObject,
    mut v_params_2668_: *mut LeanObject,
    mut v_motive_2669_: *mut LeanObject,
    mut v_discrs_2670_: *mut LeanObject,
    mut v_k_2671_: *mut LeanObject,
    mut v___x_2672_: *mut LeanObject,
    mut v_inst_2673_: *mut LeanObject,
    mut v_toBind_2674_: *mut LeanObject,
    mut v_alts_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2678_: usize = 0;
    let mut v___x_2679_: usize = 0;
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_alts_2675_);
    v___f_2676_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_2676_, 0, v_toMatcherInfo_2665_);
    lean_closure_set(v___f_2676_, 1, v_matcherName_2666_);
    lean_closure_set(v___f_2676_, 2, v_matcherLevels_2667_);
    lean_closure_set(v___f_2676_, 3, v_params_2668_);
    lean_closure_set(v___f_2676_, 4, v_motive_2669_);
    lean_closure_set(v___f_2676_, 5, v_discrs_2670_);
    lean_closure_set(v___f_2676_, 6, v_alts_2675_);
    lean_closure_set(v___f_2676_, 7, v_k_2671_);
    v___x_2677_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0;
    v_sz_2678_ = lean_array_size(v_alts_2675_);
    v___x_2679_ = 0usize;
    v___x_2680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_2672_,
        v___x_2677_,
        v_sz_2678_,
        v___x_2679_,
        v_alts_2675_,
    );
    v___x_2681_ = lean_apply_2(v_inst_2673_, lean_box(0), v___x_2680_);
    v___x_2682_ = lean_apply_4(
        v_toBind_2674_,
        lean_box(0),
        lean_box(0),
        v___x_2681_,
        v___f_2676_,
    );
    return v___x_2682_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(
    mut v___f_2702_: *mut LeanObject,
    mut v_inst_2703_: *mut LeanObject,
    mut v_inst_2704_: *mut LeanObject,
    mut v___f_2705_: *mut LeanObject,
    mut v_origAltTypes_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_altNamesTypes_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    v___x_2707_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9;
    v___x_2708_ = lean_array_get_size(v_origAltTypes_2706_);
    v___x_2709_ = lean_unsigned_to_nat(0);
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
    mut v_toMatcherInfo_2714_: *mut LeanObject,
    mut v_matcherName_2715_: *mut LeanObject,
    mut v_params_2716_: *mut LeanObject,
    mut v_motive_2717_: *mut LeanObject,
    mut v_discrs_2718_: *mut LeanObject,
    mut v_k_2719_: *mut LeanObject,
    mut v___x_2720_: *mut LeanObject,
    mut v_inst_2721_: *mut LeanObject,
    mut v_toBind_2722_: *mut LeanObject,
    mut v___f_2723_: *mut LeanObject,
    mut v_inst_2724_: *mut LeanObject,
    mut v_inst_2725_: *mut LeanObject,
    mut v_alts_2726_: *mut LeanObject,
    mut v_matcherLevels_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherPartial_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherPartial_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherPartial_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_2722_);
    lean_inc(v_inst_2721_);
    lean_inc_ref(v_discrs_2718_);
    lean_inc_ref(v_motive_2717_);
    lean_inc_ref(v_params_2716_);
    lean_inc_ref(v_matcherLevels_2727_);
    lean_inc(v_matcherName_2715_);
    v___f_2728_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19 as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_2728_, 0, v_toMatcherInfo_2714_);
    lean_closure_set(v___f_2728_, 1, v_matcherName_2715_);
    lean_closure_set(v___f_2728_, 2, v_matcherLevels_2727_);
    lean_closure_set(v___f_2728_, 3, v_params_2716_);
    lean_closure_set(v___f_2728_, 4, v_motive_2717_);
    lean_closure_set(v___f_2728_, 5, v_discrs_2718_);
    lean_closure_set(v___f_2728_, 6, v_k_2719_);
    lean_closure_set(v___f_2728_, 7, v___x_2720_);
    lean_closure_set(v___f_2728_, 8, v_inst_2721_);
    lean_closure_set(v___f_2728_, 9, v_toBind_2722_);
    v___f_2729_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2729_, 0, v___f_2723_);
    lean_closure_set(v___f_2729_, 1, v_inst_2724_);
    lean_closure_set(v___f_2729_, 2, v_inst_2725_);
    lean_closure_set(v___f_2729_, 3, v___f_2728_);
    v___x_2730_ = lean_array_to_list(v_matcherLevels_2727_);
    v___x_2731_ = l_Lean_mkConst(v_matcherName_2715_, v___x_2730_);
    v_matcherPartial_2732_ = l_Lean_mkAppN(v___x_2731_, v_params_2716_);
    lean_dec_ref(v_params_2716_);
    v_matcherPartial_2733_ = l_Lean_Expr_app___override(v_matcherPartial_2732_, v_motive_2717_);
    v_matcherPartial_2734_ = l_Lean_mkAppN(v_matcherPartial_2733_, v_discrs_2718_);
    lean_dec_ref(v_discrs_2718_);
    v___x_2735_ = lean_array_get_size(v_alts_2726_);
    v___x_2736_ = lean_alloc_closure(
        l_Lean_Meta_inferArgumentTypesN___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_2736_, 0, v___x_2735_);
    lean_closure_set(v___x_2736_, 1, v_matcherPartial_2734_);
    v___x_2737_ = lean_apply_2(v_inst_2721_, lean_box(0), v___x_2736_);
    v___x_2738_ = lean_apply_4(
        v_toBind_2722_,
        lean_box(0),
        lean_box(0),
        v___x_2737_,
        v___f_2729_,
    );
    return v___x_2738_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(
    mut v_toMatcherInfo_2739_: *mut LeanObject,
    mut v_matcherName_2740_: *mut LeanObject,
    mut v_params_2741_: *mut LeanObject,
    mut v_motive_2742_: *mut LeanObject,
    mut v_discrs_2743_: *mut LeanObject,
    mut v_k_2744_: *mut LeanObject,
    mut v___x_2745_: *mut LeanObject,
    mut v_inst_2746_: *mut LeanObject,
    mut v_toBind_2747_: *mut LeanObject,
    mut v___f_2748_: *mut LeanObject,
    mut v_inst_2749_: *mut LeanObject,
    mut v_inst_2750_: *mut LeanObject,
    mut v_alts_2751_: *mut LeanObject,
    mut v_matcherLevels_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2753_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_alts_2751_);
    return v_res_2753_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(
    mut v___f_2754_: *mut LeanObject,
    mut v_matcherLevels_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    v___x_2756_ = lean_apply_1(v___f_2754_, v_matcherLevels_2755_);
    return v___x_2756_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(
    mut v_matcherLevels_2757_: *mut LeanObject,
    mut v_val_2758_: *mut LeanObject,
    mut v_toPure_2759_: *mut LeanObject,
    mut v_toBind_2760_: *mut LeanObject,
    mut v___f_2761_: *mut LeanObject,
    mut v_uElim_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    v___x_2763_ = lean_array_set(v_matcherLevels_2757_, v_val_2758_, v_uElim_2762_);
    v___x_2764_ = lean_apply_2(v_toPure_2759_, lean_box(0), v___x_2763_);
    v___x_2765_ = lean_apply_4(
        v_toBind_2760_,
        lean_box(0),
        lean_box(0),
        v___x_2764_,
        v___f_2761_,
    );
    return v___x_2765_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(
    mut v_matcherLevels_2766_: *mut LeanObject,
    mut v_val_2767_: *mut LeanObject,
    mut v_toPure_2768_: *mut LeanObject,
    mut v_toBind_2769_: *mut LeanObject,
    mut v___f_2770_: *mut LeanObject,
    mut v_uElim_2771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2772_: *mut LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(
        v_matcherLevels_2766_,
        v_val_2767_,
        v_toPure_2768_,
        v_toBind_2769_,
        v___f_2770_,
        v_uElim_2771_,
    );
    lean_dec(v_val_2767_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(
    mut v_toMatcherInfo_2773_: *mut LeanObject,
    mut v_matcherName_2774_: *mut LeanObject,
    mut v_params_2775_: *mut LeanObject,
    mut v_discrs_2776_: *mut LeanObject,
    mut v_k_2777_: *mut LeanObject,
    mut v___x_2778_: *mut LeanObject,
    mut v_inst_2779_: *mut LeanObject,
    mut v_toBind_2780_: *mut LeanObject,
    mut v___f_2781_: *mut LeanObject,
    mut v_inst_2782_: *mut LeanObject,
    mut v_inst_2783_: *mut LeanObject,
    mut v_alts_2784_: *mut LeanObject,
    mut v_toPure_2785_: *mut LeanObject,
    mut v_matcherLevels_2786_: *mut LeanObject,
    mut v_resTy_2787_: *mut LeanObject,
    mut v_motive_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_uElimPos_x3f_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2790_: *mut LeanObject = core::ptr::null_mut();
    v_uElimPos_x3f_2789_ = lean_ctor_get(v_toMatcherInfo_2773_, 3);
    lean_inc(v_uElimPos_x3f_2789_);
    lean_inc(v_toBind_2780_);
    lean_inc(v_inst_2779_);
    v___f_2790_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed
            as *mut core::ffi::c_void,
        14,
        13,
    );
    lean_closure_set(v___f_2790_, 0, v_toMatcherInfo_2773_);
    lean_closure_set(v___f_2790_, 1, v_matcherName_2774_);
    lean_closure_set(v___f_2790_, 2, v_params_2775_);
    lean_closure_set(v___f_2790_, 3, v_motive_2788_);
    lean_closure_set(v___f_2790_, 4, v_discrs_2776_);
    lean_closure_set(v___f_2790_, 5, v_k_2777_);
    lean_closure_set(v___f_2790_, 6, v___x_2778_);
    lean_closure_set(v___f_2790_, 7, v_inst_2779_);
    lean_closure_set(v___f_2790_, 8, v_toBind_2780_);
    lean_closure_set(v___f_2790_, 9, v___f_2781_);
    lean_closure_set(v___f_2790_, 10, v_inst_2782_);
    lean_closure_set(v___f_2790_, 11, v_inst_2783_);
    lean_closure_set(v___f_2790_, 12, v_alts_2784_);
    if lean_obj_tag(v_uElimPos_x3f_2789_) == 0 {
        let mut v___f_2791_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_resTy_2787_);
        lean_dec(v_inst_2779_);
        v___f_2791_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_2791_, 0, v___f_2790_);
        v___x_2792_ = lean_apply_2(v_toPure_2785_, lean_box(0), v_matcherLevels_2786_);
        v___x_2793_ = lean_apply_4(
            v_toBind_2780_,
            lean_box(0),
            lean_box(0),
            v___x_2792_,
            v___f_2791_,
        );
        return v___x_2793_;
    } else {
        let mut v_val_2794_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2795_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2796_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
        v_val_2794_ = lean_ctor_get(v_uElimPos_x3f_2789_, 0);
        lean_inc(v_val_2794_);
        lean_dec_ref_known(v_uElimPos_x3f_2789_, 1);
        v___f_2795_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_2795_, 0, v___f_2790_);
        lean_inc(v_toBind_2780_);
        v___f_2796_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_2796_, 0, v_matcherLevels_2786_);
        lean_closure_set(v___f_2796_, 1, v_val_2794_);
        lean_closure_set(v___f_2796_, 2, v_toPure_2785_);
        lean_closure_set(v___f_2796_, 3, v_toBind_2780_);
        lean_closure_set(v___f_2796_, 4, v___f_2795_);
        v___x_2797_ =
            lean_alloc_closure(l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void, 6, 1);
        lean_closure_set(v___x_2797_, 0, v_resTy_2787_);
        v___x_2798_ = lean_apply_2(v_inst_2779_, lean_box(0), v___x_2797_);
        v___x_2799_ = lean_apply_4(
            v_toBind_2780_,
            lean_box(0),
            lean_box(0),
            v___x_2798_,
            v___f_2796_,
        );
        return v___x_2799_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(
    mut v_toMatcherInfo_2800_: *mut LeanObject,
    mut v_matcherName_2801_: *mut LeanObject,
    mut v_params_2802_: *mut LeanObject,
    mut v_k_2803_: *mut LeanObject,
    mut v___x_2804_: *mut LeanObject,
    mut v_inst_2805_: *mut LeanObject,
    mut v_toBind_2806_: *mut LeanObject,
    mut v___f_2807_: *mut LeanObject,
    mut v_inst_2808_: *mut LeanObject,
    mut v_inst_2809_: *mut LeanObject,
    mut v_alts_2810_: *mut LeanObject,
    mut v_toPure_2811_: *mut LeanObject,
    mut v_matcherLevels_2812_: *mut LeanObject,
    mut v_resTy_2813_: *mut LeanObject,
    mut v___x_2814_: *mut LeanObject,
    mut v_motive_2815_: *mut LeanObject,
    mut v___f_2816_: *mut LeanObject,
    mut v_discrs_2817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: u8 = 0;
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_2806_);
    lean_inc(v_inst_2805_);
    lean_inc_ref(v___x_2804_);
    v___f_2818_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23 as *mut core::ffi::c_void,
        16,
        15,
    );
    lean_closure_set(v___f_2818_, 0, v_toMatcherInfo_2800_);
    lean_closure_set(v___f_2818_, 1, v_matcherName_2801_);
    lean_closure_set(v___f_2818_, 2, v_params_2802_);
    lean_closure_set(v___f_2818_, 3, v_discrs_2817_);
    lean_closure_set(v___f_2818_, 4, v_k_2803_);
    lean_closure_set(v___f_2818_, 5, v___x_2804_);
    lean_closure_set(v___f_2818_, 6, v_inst_2805_);
    lean_closure_set(v___f_2818_, 7, v_toBind_2806_);
    lean_closure_set(v___f_2818_, 8, v___f_2807_);
    lean_closure_set(v___f_2818_, 9, v_inst_2808_);
    lean_closure_set(v___f_2818_, 10, v_inst_2809_);
    lean_closure_set(v___f_2818_, 11, v_alts_2810_);
    lean_closure_set(v___f_2818_, 12, v_toPure_2811_);
    lean_closure_set(v___f_2818_, 13, v_matcherLevels_2812_);
    lean_closure_set(v___f_2818_, 14, v_resTy_2813_);
    v___x_2819_ = 0;
    v___x_2820_ = l_Lean_Meta_lambdaTelescope___redArg(
        v___x_2814_,
        v___x_2804_,
        v_motive_2815_,
        v___f_2816_,
        v___x_2819_,
    );
    v___x_2821_ = lean_apply_2(v_inst_2805_, lean_box(0), v___x_2820_);
    v___x_2822_ = lean_apply_4(
        v_toBind_2806_,
        lean_box(0),
        lean_box(0),
        v___x_2821_,
        v___f_2818_,
    );
    return v___x_2822_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMatcherInfo_2823_: *mut LeanObject = *_args.add(0);
    let mut v_matcherName_2824_: *mut LeanObject = *_args.add(1);
    let mut v_params_2825_: *mut LeanObject = *_args.add(2);
    let mut v_k_2826_: *mut LeanObject = *_args.add(3);
    let mut v___x_2827_: *mut LeanObject = *_args.add(4);
    let mut v_inst_2828_: *mut LeanObject = *_args.add(5);
    let mut v_toBind_2829_: *mut LeanObject = *_args.add(6);
    let mut v___f_2830_: *mut LeanObject = *_args.add(7);
    let mut v_inst_2831_: *mut LeanObject = *_args.add(8);
    let mut v_inst_2832_: *mut LeanObject = *_args.add(9);
    let mut v_alts_2833_: *mut LeanObject = *_args.add(10);
    let mut v_toPure_2834_: *mut LeanObject = *_args.add(11);
    let mut v_matcherLevels_2835_: *mut LeanObject = *_args.add(12);
    let mut v_resTy_2836_: *mut LeanObject = *_args.add(13);
    let mut v___x_2837_: *mut LeanObject = *_args.add(14);
    let mut v_motive_2838_: *mut LeanObject = *_args.add(15);
    let mut v___f_2839_: *mut LeanObject = *_args.add(16);
    let mut v_discrs_2840_: *mut LeanObject = *_args.add(17);
    let mut v_res_2841_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_2842_: *mut LeanObject,
    mut v_inst_2843_: *mut LeanObject,
    mut v___f_2844_: *mut LeanObject,
    mut v_discrNamesTypes_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2846_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    v___x_2848_ = l_instMonadEIO(lean_box(0));
    return v___x_2848_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    v___x_2849_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    v___x_2858_ = lean_unsigned_to_nat(0);
    v___x_2859_ = l_Lean_Level_ofNat(v___x_2858_);
    return v___x_2859_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    v___x_2860_ = lean_obj_once(
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
    mut v_inst_2863_: *mut LeanObject,
    mut v_inst_2864_: *mut LeanObject,
    mut v_inst_2865_: *mut LeanObject,
    mut v_info_2866_: *mut LeanObject,
    mut v_resTy_2867_: *mut LeanObject,
    mut v_k_2868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v_toFunctor_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___f_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherApp_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMatcherInfo_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherName_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherLevels_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v_unused_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_unused_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2869_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1,
                );
                v_toApplicative_2870_ = lean_ctor_get(v___x_2869_, 0);
                v_toFunctor_2871_ = lean_ctor_get(v_toApplicative_2870_, 0);
                v_toSeq_2872_ = lean_ctor_get(v_toApplicative_2870_, 2);
                v_toSeqLeft_2873_ = lean_ctor_get(v_toApplicative_2870_, 3);
                v_toSeqRight_2874_ = lean_ctor_get(v_toApplicative_2870_, 4);
                v___f_2875_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2;
                v___f_2876_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3;
                lean_inc_ref_n(v_toFunctor_2871_, 2);
                v___f_2877_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2877_, 0, v_toFunctor_2871_);
                v___f_2878_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2878_, 0, v_toFunctor_2871_);
                v___x_2879_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2879_, 0, v___f_2877_);
                lean_ctor_set(v___x_2879_, 1, v___f_2878_);
                lean_inc(v_toSeqRight_2874_);
                v___f_2880_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2880_, 0, v_toSeqRight_2874_);
                lean_inc(v_toSeqLeft_2873_);
                v___f_2881_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2881_, 0, v_toSeqLeft_2873_);
                lean_inc(v_toSeq_2872_);
                v___f_2882_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2882_, 0, v_toSeq_2872_);
                v___x_2883_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2883_, 0, v___x_2879_);
                lean_ctor_set(v___x_2883_, 1, v___f_2875_);
                lean_ctor_set(v___x_2883_, 2, v___f_2882_);
                lean_ctor_set(v___x_2883_, 3, v___f_2881_);
                lean_ctor_set(v___x_2883_, 4, v___f_2880_);
                v___x_2884_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2884_, 0, v___x_2883_);
                lean_ctor_set(v___x_2884_, 1, v___f_2876_);
                v___x_2885_ = l_StateRefT_x27_instMonad___redArg(v___x_2884_);
                v___x_2886_ =
                    lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_2886_, 0, lean_box(0));
                lean_closure_set(v___x_2886_, 1, lean_box(0));
                lean_closure_set(v___x_2886_, 2, v___x_2885_);
                v___x_2887_ = l_instMonadControlTOfPure___redArg(v___x_2886_);
                v_toApplicative_2888_ = lean_ctor_get(v___x_2869_, 0);
                v_toFunctor_2889_ = lean_ctor_get(v_toApplicative_2888_, 0);
                v_toSeq_2890_ = lean_ctor_get(v_toApplicative_2888_, 2);
                v_toSeqLeft_2891_ = lean_ctor_get(v_toApplicative_2888_, 3);
                v_toSeqRight_2892_ = lean_ctor_get(v_toApplicative_2888_, 4);
                lean_inc_ref_n(v_toFunctor_2889_, 2);
                v___f_2893_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2893_, 0, v_toFunctor_2889_);
                v___f_2894_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2894_, 0, v_toFunctor_2889_);
                v___x_2895_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2895_, 0, v___f_2893_);
                lean_ctor_set(v___x_2895_, 1, v___f_2894_);
                lean_inc(v_toSeqRight_2892_);
                v___f_2896_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2896_, 0, v_toSeqRight_2892_);
                lean_inc(v_toSeqLeft_2891_);
                v___f_2897_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2897_, 0, v_toSeqLeft_2891_);
                lean_inc(v_toSeq_2890_);
                v___f_2898_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2898_, 0, v_toSeq_2890_);
                v___x_2899_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2899_, 0, v___x_2895_);
                lean_ctor_set(v___x_2899_, 1, v___f_2875_);
                lean_ctor_set(v___x_2899_, 2, v___f_2898_);
                lean_ctor_set(v___x_2899_, 3, v___f_2897_);
                lean_ctor_set(v___x_2899_, 4, v___f_2896_);
                v___x_2900_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2900_, 0, v___x_2899_);
                lean_ctor_set(v___x_2900_, 1, v___f_2876_);
                v___x_2901_ = l_StateRefT_x27_instMonad___redArg(v___x_2900_);
                v_toApplicative_2902_ = lean_ctor_get(v___x_2901_, 0);
                v_isSharedCheck_2960_ = (!lean_is_exclusive(v___x_2901_)) as u8;
                if v_isSharedCheck_2960_ == 0 {
                    v_unused_2961_ = lean_ctor_get(v___x_2901_, 1);
                    lean_dec(v_unused_2961_);
                    v___x_2904_ = v___x_2901_;
                    v_isShared_2905_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2902_);
                    lean_dec(v___x_2901_);
                    v___x_2904_ = lean_box(0);
                    v_isShared_2905_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2906_ = lean_ctor_get(v_toApplicative_2902_, 0);
                v_toSeq_2907_ = lean_ctor_get(v_toApplicative_2902_, 2);
                v_toSeqLeft_2908_ = lean_ctor_get(v_toApplicative_2902_, 3);
                v_toSeqRight_2909_ = lean_ctor_get(v_toApplicative_2902_, 4);
                v_isSharedCheck_2958_ = (!lean_is_exclusive(v_toApplicative_2902_)) as u8;
                if v_isSharedCheck_2958_ == 0 {
                    v_unused_2959_ = lean_ctor_get(v_toApplicative_2902_, 1);
                    lean_dec(v_unused_2959_);
                    v___x_2911_ = v_toApplicative_2902_;
                    v_isShared_2912_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2909_);
                    lean_inc(v_toSeqLeft_2908_);
                    lean_inc(v_toSeq_2907_);
                    lean_inc(v_toFunctor_2906_);
                    lean_dec(v_toApplicative_2902_);
                    v___x_2911_ = lean_box(0);
                    v_isShared_2912_ = v_isSharedCheck_2958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2913_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4;
                v___f_2914_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5;
                lean_inc_ref(v_toFunctor_2906_);
                v___f_2915_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2915_, 0, v_toFunctor_2906_);
                v___f_2916_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2916_, 0, v_toFunctor_2906_);
                v___x_2917_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2917_, 0, v___f_2915_);
                lean_ctor_set(v___x_2917_, 1, v___f_2916_);
                v___f_2918_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2918_, 0, v_toSeqRight_2909_);
                v___f_2919_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2919_, 0, v_toSeqLeft_2908_);
                v___f_2920_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2920_, 0, v_toSeq_2907_);
                if v_isShared_2912_ == 0 {
                    lean_ctor_set(v___x_2911_, 4, v___f_2918_);
                    lean_ctor_set(v___x_2911_, 3, v___f_2919_);
                    lean_ctor_set(v___x_2911_, 2, v___f_2920_);
                    lean_ctor_set(v___x_2911_, 1, v___f_2913_);
                    lean_ctor_set(v___x_2911_, 0, v___x_2917_);
                    v___x_2922_ = v___x_2911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2917_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 1, v___f_2913_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 2, v___f_2920_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 3, v___f_2919_);
                    lean_ctor_set(v_reuseFailAlloc_2957_, 4, v___f_2918_);
                    v___x_2922_ = v_reuseFailAlloc_2957_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2905_ == 0 {
                    lean_ctor_set(v___x_2904_, 1, v___f_2914_);
                    lean_ctor_set(v___x_2904_, 0, v___x_2922_);
                    v___x_2924_ = v___x_2904_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2956_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 0, v___x_2922_);
                    lean_ctor_set(v_reuseFailAlloc_2956_, 1, v___f_2914_);
                    v___x_2924_ = v_reuseFailAlloc_2956_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                match lean_obj_tag(v_info_2866_) {
                    0 => {
                        lean_dec_ref_known(v_info_2866_, 1);
                        lean_dec_ref(v___x_2924_);
                        lean_dec_ref(v___x_2887_);
                        v_toBind_2925_ = lean_ctor_get(v_inst_2865_, 1);
                        lean_inc_ref(v_inst_2865_);
                        lean_inc_ref(v_inst_2864_);
                        lean_inc(v_toBind_2925_);
                        v___f_2926_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4
                                as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        lean_closure_set(v___f_2926_, 0, v_resTy_2867_);
                        lean_closure_set(v___f_2926_, 1, v_k_2868_);
                        lean_closure_set(v___f_2926_, 2, v_inst_2863_);
                        lean_closure_set(v___f_2926_, 3, v_toBind_2925_);
                        lean_closure_set(v___f_2926_, 4, v_inst_2864_);
                        lean_closure_set(v___f_2926_, 5, v_inst_2865_);
                        v___x_2927_ =
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7;
                        v___x_2928_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once), _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
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
                        lean_dec_ref_known(v_info_2866_, 1);
                        lean_dec_ref(v___x_2924_);
                        lean_dec_ref(v___x_2887_);
                        v_toBind_2930_ = lean_ctor_get(v_inst_2865_, 1);
                        lean_inc_ref(v_inst_2865_);
                        lean_inc_ref(v_inst_2864_);
                        lean_inc(v_toBind_2930_);
                        v___f_2931_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13
                                as *mut core::ffi::c_void,
                            7,
                            6,
                        );
                        lean_closure_set(v___f_2931_, 0, v_resTy_2867_);
                        lean_closure_set(v___f_2931_, 1, v_k_2868_);
                        lean_closure_set(v___f_2931_, 2, v_inst_2863_);
                        lean_closure_set(v___f_2931_, 3, v_toBind_2930_);
                        lean_closure_set(v___f_2931_, 4, v_inst_2864_);
                        lean_closure_set(v___f_2931_, 5, v_inst_2865_);
                        v___x_2932_ =
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7;
                        v___x_2933_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once), _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
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
                        v_toApplicative_2935_ = lean_ctor_get(v_inst_2865_, 0);
                        v_matcherApp_2936_ = lean_ctor_get(v_info_2866_, 0);
                        lean_inc_ref(v_matcherApp_2936_);
                        lean_dec_ref_known(v_info_2866_, 1);
                        v_toBind_2937_ = lean_ctor_get(v_inst_2865_, 1);
                        lean_inc_n(v_toBind_2937_, 3);
                        v_toPure_2938_ = lean_ctor_get(v_toApplicative_2935_, 1);
                        v_toMatcherInfo_2939_ = lean_ctor_get(v_matcherApp_2936_, 0);
                        lean_inc_ref(v_toMatcherInfo_2939_);
                        v_matcherName_2940_ = lean_ctor_get(v_matcherApp_2936_, 1);
                        lean_inc(v_matcherName_2940_);
                        v_matcherLevels_2941_ = lean_ctor_get(v_matcherApp_2936_, 2);
                        lean_inc_ref(v_matcherLevels_2941_);
                        v_params_2942_ = lean_ctor_get(v_matcherApp_2936_, 3);
                        lean_inc_ref(v_params_2942_);
                        v_motive_2943_ = lean_ctor_get(v_matcherApp_2936_, 4);
                        lean_inc_ref(v_motive_2943_);
                        v_discrs_2944_ = lean_ctor_get(v_matcherApp_2936_, 5);
                        lean_inc_ref(v_discrs_2944_);
                        v_alts_2945_ = lean_ctor_get(v_matcherApp_2936_, 6);
                        lean_inc_ref(v_alts_2945_);
                        lean_dec_ref(v_matcherApp_2936_);
                        lean_inc_ref(v_resTy_2867_);
                        v___f_2946_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed
                                as *mut core::ffi::c_void,
                            8,
                            1,
                        );
                        lean_closure_set(v___f_2946_, 0, v_resTy_2867_);
                        v___f_2947_ =
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10;
                        lean_inc(v_inst_2863_);
                        lean_inc_n(v_toPure_2938_, 2);
                        v___f_2948_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17
                                as *mut core::ffi::c_void,
                            6,
                            3,
                        );
                        lean_closure_set(v___f_2948_, 0, v_toPure_2938_);
                        lean_closure_set(v___f_2948_, 1, v_inst_2863_);
                        lean_closure_set(v___f_2948_, 2, v_toBind_2937_);
                        lean_inc_ref_n(v_inst_2865_, 2);
                        lean_inc_ref(v_inst_2864_);
                        v___f_2949_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___boxed
                                as *mut core::ffi::c_void,
                            18,
                            17,
                        );
                        lean_closure_set(v___f_2949_, 0, v_toMatcherInfo_2939_);
                        lean_closure_set(v___f_2949_, 1, v_matcherName_2940_);
                        lean_closure_set(v___f_2949_, 2, v_params_2942_);
                        lean_closure_set(v___f_2949_, 3, v_k_2868_);
                        lean_closure_set(v___f_2949_, 4, v___x_2924_);
                        lean_closure_set(v___f_2949_, 5, v_inst_2863_);
                        lean_closure_set(v___f_2949_, 6, v_toBind_2937_);
                        lean_closure_set(v___f_2949_, 7, v___f_2947_);
                        lean_closure_set(v___f_2949_, 8, v_inst_2864_);
                        lean_closure_set(v___f_2949_, 9, v_inst_2865_);
                        lean_closure_set(v___f_2949_, 10, v_alts_2945_);
                        lean_closure_set(v___f_2949_, 11, v_toPure_2938_);
                        lean_closure_set(v___f_2949_, 12, v_matcherLevels_2941_);
                        lean_closure_set(v___f_2949_, 13, v_resTy_2867_);
                        lean_closure_set(v___f_2949_, 14, v___x_2887_);
                        lean_closure_set(v___f_2949_, 15, v_motive_2943_);
                        lean_closure_set(v___f_2949_, 16, v___f_2946_);
                        v___f_2950_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        lean_closure_set(v___f_2950_, 0, v_inst_2864_);
                        lean_closure_set(v___f_2950_, 1, v_inst_2865_);
                        lean_closure_set(v___f_2950_, 2, v___f_2949_);
                        v___x_2951_ = lean_array_get_size(v_discrs_2944_);
                        v___x_2952_ = lean_unsigned_to_nat(0);
                        v___x_2953_ = lean_mk_empty_array_with_capacity(v___x_2951_);
                        v___x_2954_ = l_Array_mapFinIdxM_map___redArg(
                            v_inst_2865_,
                            v_discrs_2944_,
                            v___f_2948_,
                            v___x_2951_,
                            v___x_2952_,
                            v___x_2953_,
                        );
                        v___x_2955_ = lean_apply_4(
                            v_toBind_2937_,
                            lean_box(0),
                            lean_box(0),
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
    mut v_n_2962_: *mut LeanObject,
    mut v_00_u03b1_2963_: *mut LeanObject,
    mut v_inst_2964_: *mut LeanObject,
    mut v_inst_2965_: *mut LeanObject,
    mut v_inst_2966_: *mut LeanObject,
    mut v_inst_2967_: *mut LeanObject,
    mut v_info_2968_: *mut LeanObject,
    mut v_resTy_2969_: *mut LeanObject,
    mut v_k_2970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_2972_: *mut LeanObject,
    mut v_00_u03b1_2973_: *mut LeanObject,
    mut v_inst_2974_: *mut LeanObject,
    mut v_inst_2975_: *mut LeanObject,
    mut v_inst_2976_: *mut LeanObject,
    mut v_inst_2977_: *mut LeanObject,
    mut v_info_2978_: *mut LeanObject,
    mut v_resTy_2979_: *mut LeanObject,
    mut v_k_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2981_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_inst_2977_);
    return v_res_2981_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(
    mut v_u_2982_: *mut LeanObject,
    mut v_resTy_2983_: *mut LeanObject,
    mut v_c_2984_: *mut LeanObject,
    mut v_h_2985_: *mut LeanObject,
    mut v_t_2986_: *mut LeanObject,
    mut v_toPure_2987_: *mut LeanObject,
    mut v_e_2988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1;
    v___x_2990_ = lean_box(0);
    v___x_2991_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2991_, 0, v_u_2982_);
    lean_ctor_set(v___x_2991_, 1, v___x_2990_);
    v___x_2992_ = l_Lean_mkConst(v___x_2989_, v___x_2991_);
    v___x_2993_ = l_Lean_mkApp5(
        v___x_2992_,
        v_resTy_2983_,
        v_c_2984_,
        v_h_2985_,
        v_t_2986_,
        v_e_2988_,
    );
    v___x_2994_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_2993_);
    return v___x_2994_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(
    mut v_u_2998_: *mut LeanObject,
    mut v_resTy_2999_: *mut LeanObject,
    mut v_c_3000_: *mut LeanObject,
    mut v_h_3001_: *mut LeanObject,
    mut v_toPure_3002_: *mut LeanObject,
    mut v_onAlt_3003_: *mut LeanObject,
    mut v___x_3004_: *mut LeanObject,
    mut v___x_3005_: *mut LeanObject,
    mut v_toBind_3006_: *mut LeanObject,
    mut v_t_3007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_resTy_2999_);
    v___f_3008_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3008_, 0, v_u_2998_);
    lean_closure_set(v___f_3008_, 1, v_resTy_2999_);
    lean_closure_set(v___f_3008_, 2, v_c_3000_);
    lean_closure_set(v___f_3008_, 3, v_h_3001_);
    lean_closure_set(v___f_3008_, 4, v_t_3007_);
    lean_closure_set(v___f_3008_, 5, v_toPure_3002_);
    v___x_3009_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1;
    v___x_3010_ = lean_apply_4(
        v_onAlt_3003_,
        v___x_3009_,
        v_resTy_2999_,
        v___x_3004_,
        v___x_3005_,
    );
    v___x_3011_ = lean_apply_4(
        v_toBind_3006_,
        lean_box(0),
        lean_box(0),
        v___x_3010_,
        v___f_3008_,
    );
    return v___x_3011_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(
    mut v___x_3012_: *mut LeanObject,
    mut v_useSplitter_3013_: u8,
    mut v_inst_3014_: *mut LeanObject,
    mut v_____do__lift_3015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    v___x_3016_ = 0;
    v___x_3017_ = 1;
    v___x_3018_ = lean_box((v___x_3016_) as usize);
    v___x_3019_ = lean_box((v_useSplitter_3013_) as usize);
    v___x_3020_ = lean_box((v___x_3016_) as usize);
    v___x_3021_ = lean_box((v_useSplitter_3013_) as usize);
    v___x_3022_ = lean_box((v___x_3017_) as usize);
    v___x_3023_ = lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    lean_closure_set(v___x_3023_, 0, v___x_3012_);
    lean_closure_set(v___x_3023_, 1, v_____do__lift_3015_);
    lean_closure_set(v___x_3023_, 2, v___x_3018_);
    lean_closure_set(v___x_3023_, 3, v___x_3019_);
    lean_closure_set(v___x_3023_, 4, v___x_3020_);
    lean_closure_set(v___x_3023_, 5, v___x_3021_);
    lean_closure_set(v___x_3023_, 6, v___x_3022_);
    v___x_3024_ = lean_apply_2(v_inst_3014_, lean_box(0), v___x_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(
    mut v___x_3025_: *mut LeanObject,
    mut v_useSplitter_3026_: *mut LeanObject,
    mut v_inst_3027_: *mut LeanObject,
    mut v_____do__lift_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useSplitter_boxed_3029_: u8 = 0;
    let mut v_res_3030_: *mut LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3029_ = (lean_unbox(v_useSplitter_3026_) as u8);
    v_res_3030_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(
        v___x_3025_,
        v_useSplitter_boxed_3029_,
        v_inst_3027_,
        v_____do__lift_3028_,
    );
    return v_res_3030_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(
    mut v___x_3034_: *mut LeanObject,
    mut v_useSplitter_3035_: u8,
    mut v_inst_3036_: *mut LeanObject,
    mut v_onAlt_3037_: *mut LeanObject,
    mut v_resTy_3038_: *mut LeanObject,
    mut v_toBind_3039_: *mut LeanObject,
    mut v_h_3040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    v___x_3041_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1;
    v___x_3042_ = lean_unsigned_to_nat(0);
    v___x_3043_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3044_ = lean_mk_empty_array_with_capacity(v___x_3034_);
    v___x_3045_ = lean_array_push(v___x_3044_, v_h_3040_);
    v___x_3046_ = lean_box((v_useSplitter_3035_) as usize);
    lean_inc_ref(v___x_3045_);
    v___f_3047_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3047_, 0, v___x_3045_);
    lean_closure_set(v___f_3047_, 1, v___x_3046_);
    lean_closure_set(v___f_3047_, 2, v_inst_3036_);
    v___x_3048_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3048_, 0, v___x_3043_);
    lean_ctor_set(v___x_3048_, 1, v___x_3045_);
    lean_ctor_set(v___x_3048_, 2, v___x_3043_);
    lean_ctor_set(v___x_3048_, 3, v___x_3043_);
    lean_ctor_set(v___x_3048_, 4, v___x_3043_);
    v___x_3049_ = lean_apply_4(
        v_onAlt_3037_,
        v___x_3041_,
        v_resTy_3038_,
        v___x_3042_,
        v___x_3048_,
    );
    v___x_3050_ = lean_apply_4(
        v_toBind_3039_,
        lean_box(0),
        lean_box(0),
        v___x_3049_,
        v___f_3047_,
    );
    return v___x_3050_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(
    mut v___x_3051_: *mut LeanObject,
    mut v_useSplitter_3052_: *mut LeanObject,
    mut v_inst_3053_: *mut LeanObject,
    mut v_onAlt_3054_: *mut LeanObject,
    mut v_resTy_3055_: *mut LeanObject,
    mut v_toBind_3056_: *mut LeanObject,
    mut v_h_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useSplitter_boxed_3058_: u8 = 0;
    let mut v_res_3059_: *mut LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3058_ = (lean_unbox(v_useSplitter_3052_) as u8);
    v_res_3059_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(
        v___x_3051_,
        v_useSplitter_boxed_3058_,
        v_inst_3053_,
        v_onAlt_3054_,
        v_resTy_3055_,
        v_toBind_3056_,
        v_h_3057_,
    );
    lean_dec(v___x_3051_);
    return v_res_3059_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(
    mut v___x_3060_: *mut LeanObject,
    mut v_useSplitter_3061_: u8,
    mut v_inst_3062_: *mut LeanObject,
    mut v_onAlt_3063_: *mut LeanObject,
    mut v_resTy_3064_: *mut LeanObject,
    mut v_toBind_3065_: *mut LeanObject,
    mut v_h_3066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    v___x_3067_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1;
    v___x_3068_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3069_ = lean_mk_empty_array_with_capacity(v___x_3060_);
    v___x_3070_ = lean_array_push(v___x_3069_, v_h_3066_);
    v___x_3071_ = lean_box((v_useSplitter_3061_) as usize);
    lean_inc_ref(v___x_3070_);
    v___f_3072_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3072_, 0, v___x_3070_);
    lean_closure_set(v___f_3072_, 1, v___x_3071_);
    lean_closure_set(v___f_3072_, 2, v_inst_3062_);
    v___x_3073_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3073_, 0, v___x_3068_);
    lean_ctor_set(v___x_3073_, 1, v___x_3070_);
    lean_ctor_set(v___x_3073_, 2, v___x_3068_);
    lean_ctor_set(v___x_3073_, 3, v___x_3068_);
    lean_ctor_set(v___x_3073_, 4, v___x_3068_);
    v___x_3074_ = lean_apply_4(
        v_onAlt_3063_,
        v___x_3067_,
        v_resTy_3064_,
        v___x_3060_,
        v___x_3073_,
    );
    v___x_3075_ = lean_apply_4(
        v_toBind_3065_,
        lean_box(0),
        lean_box(0),
        v___x_3074_,
        v___f_3072_,
    );
    return v___x_3075_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(
    mut v___x_3076_: *mut LeanObject,
    mut v_useSplitter_3077_: *mut LeanObject,
    mut v_inst_3078_: *mut LeanObject,
    mut v_onAlt_3079_: *mut LeanObject,
    mut v_resTy_3080_: *mut LeanObject,
    mut v_toBind_3081_: *mut LeanObject,
    mut v_h_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useSplitter_boxed_3083_: u8 = 0;
    let mut v_res_3084_: *mut LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3083_ = (lean_unbox(v_useSplitter_3077_) as u8);
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
    mut v_u_3085_: *mut LeanObject,
    mut v_resTy_3086_: *mut LeanObject,
    mut v_c_3087_: *mut LeanObject,
    mut v_h_3088_: *mut LeanObject,
    mut v_t_3089_: *mut LeanObject,
    mut v_toPure_3090_: *mut LeanObject,
    mut v_e_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    v___x_3092_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1;
    v___x_3093_ = lean_box(0);
    v___x_3094_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3094_, 0, v_u_3085_);
    lean_ctor_set(v___x_3094_, 1, v___x_3093_);
    v___x_3095_ = l_Lean_mkConst(v___x_3092_, v___x_3094_);
    v___x_3096_ = l_Lean_mkApp5(
        v___x_3095_,
        v_resTy_3086_,
        v_c_3087_,
        v_h_3088_,
        v_t_3089_,
        v_e_3091_,
    );
    v___x_3097_ = lean_apply_2(v_toPure_3090_, lean_box(0), v___x_3096_);
    return v___x_3097_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(
    mut v_u_3098_: *mut LeanObject,
    mut v_resTy_3099_: *mut LeanObject,
    mut v_c_3100_: *mut LeanObject,
    mut v_h_3101_: *mut LeanObject,
    mut v_toPure_3102_: *mut LeanObject,
    mut v_inst_3103_: *mut LeanObject,
    mut v_inst_3104_: *mut LeanObject,
    mut v_n_3105_: *mut LeanObject,
    mut v___x_3106_: u8,
    mut v___f_3107_: *mut LeanObject,
    mut v___x_3108_: u8,
    mut v_toBind_3109_: *mut LeanObject,
    mut v_t_3110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_c_3100_);
    v___f_3111_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3111_, 0, v_u_3098_);
    lean_closure_set(v___f_3111_, 1, v_resTy_3099_);
    lean_closure_set(v___f_3111_, 2, v_c_3100_);
    lean_closure_set(v___f_3111_, 3, v_h_3101_);
    lean_closure_set(v___f_3111_, 4, v_t_3110_);
    lean_closure_set(v___f_3111_, 5, v_toPure_3102_);
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
    v___x_3114_ = lean_apply_4(
        v_toBind_3109_,
        lean_box(0),
        lean_box(0),
        v___x_3113_,
        v___f_3111_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(
    mut v_u_3115_: *mut LeanObject,
    mut v_resTy_3116_: *mut LeanObject,
    mut v_c_3117_: *mut LeanObject,
    mut v_h_3118_: *mut LeanObject,
    mut v_toPure_3119_: *mut LeanObject,
    mut v_inst_3120_: *mut LeanObject,
    mut v_inst_3121_: *mut LeanObject,
    mut v_n_3122_: *mut LeanObject,
    mut v___x_3123_: *mut LeanObject,
    mut v___f_3124_: *mut LeanObject,
    mut v___x_3125_: *mut LeanObject,
    mut v_toBind_3126_: *mut LeanObject,
    mut v_t_3127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1249__boxed_3128_: u8 = 0;
    let mut v___x_1251__boxed_3129_: u8 = 0;
    let mut v_res_3130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1249__boxed_3128_ = (lean_unbox(v___x_3123_) as u8);
    v___x_1251__boxed_3129_ = (lean_unbox(v___x_3125_) as u8);
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
    mut v_u_3131_: *mut LeanObject,
    mut v_resTy_3132_: *mut LeanObject,
    mut v_c_3133_: *mut LeanObject,
    mut v_h_3134_: *mut LeanObject,
    mut v_toPure_3135_: *mut LeanObject,
    mut v_inst_3136_: *mut LeanObject,
    mut v_inst_3137_: *mut LeanObject,
    mut v___f_3138_: *mut LeanObject,
    mut v_toBind_3139_: *mut LeanObject,
    mut v___f_3140_: *mut LeanObject,
    mut v_n_3141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3142_: u8 = 0;
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    v___x_3142_ = 0;
    v___x_3143_ = 0;
    v___x_3144_ = lean_box((v___x_3142_) as usize);
    v___x_3145_ = lean_box((v___x_3143_) as usize);
    lean_inc(v_toBind_3139_);
    lean_inc(v_n_3141_);
    lean_inc_ref(v_inst_3137_);
    lean_inc_ref(v_inst_3136_);
    lean_inc_ref(v_c_3133_);
    v___f_3146_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed
            as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_3146_, 0, v_u_3131_);
    lean_closure_set(v___f_3146_, 1, v_resTy_3132_);
    lean_closure_set(v___f_3146_, 2, v_c_3133_);
    lean_closure_set(v___f_3146_, 3, v_h_3134_);
    lean_closure_set(v___f_3146_, 4, v_toPure_3135_);
    lean_closure_set(v___f_3146_, 5, v_inst_3136_);
    lean_closure_set(v___f_3146_, 6, v_inst_3137_);
    lean_closure_set(v___f_3146_, 7, v_n_3141_);
    lean_closure_set(v___f_3146_, 8, v___x_3144_);
    lean_closure_set(v___f_3146_, 9, v___f_3138_);
    lean_closure_set(v___f_3146_, 10, v___x_3145_);
    lean_closure_set(v___f_3146_, 11, v_toBind_3139_);
    v___x_3147_ = l_Lean_Meta_withLocalDecl___redArg(
        v_inst_3136_,
        v_inst_3137_,
        v_n_3141_,
        v___x_3142_,
        v_c_3133_,
        v___f_3140_,
        v___x_3143_,
    );
    v___x_3148_ = lean_apply_4(
        v_toBind_3139_,
        lean_box(0),
        lean_box(0),
        v___x_3147_,
        v___f_3146_,
    );
    return v___x_3148_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(
    mut v___x_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Lean_Core_mkFreshUserName(v___x_3149_, v___y_3152_, v___y_3153_);
    return v___x_3155_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(
    mut v___x_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
    mut v___y_3158_: *mut LeanObject,
    mut v___y_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3162_: *mut LeanObject = core::ptr::null_mut();
    v_res_3162_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(
        v___x_3156_,
        v___y_3157_,
        v___y_3158_,
        v___y_3159_,
        v___y_3160_,
    );
    lean_dec(v___y_3160_);
    lean_dec_ref(v___y_3159_);
    lean_dec(v___y_3158_);
    lean_dec_ref(v___y_3157_);
    return v_res_3162_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(
    mut v_e_3170_: *mut LeanObject,
    mut v_useSplitter_3171_: u8,
    mut v_resTy_3172_: *mut LeanObject,
    mut v_toPure_3173_: *mut LeanObject,
    mut v_onAlt_3174_: *mut LeanObject,
    mut v_toBind_3175_: *mut LeanObject,
    mut v_inst_3176_: *mut LeanObject,
    mut v_inst_3177_: *mut LeanObject,
    mut v_inst_3178_: *mut LeanObject,
    mut v_u_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_3188_: *mut LeanObject = core::ptr::null_mut();
    v___x_3180_ = lean_unsigned_to_nat(1);
    v___x_3181_ = l_Lean_Expr_getAppNumArgs(v_e_3170_);
    v___x_3182_ = lean_nat_sub(v___x_3181_, v___x_3180_);
    v___x_3183_ = lean_nat_sub(v___x_3182_, v___x_3180_);
    lean_dec(v___x_3182_);
    v_c_3184_ = l_Lean_Expr_getRevArg_x21(v_e_3170_, v___x_3183_);
    v___x_3185_ = lean_unsigned_to_nat(2);
    v___x_3186_ = lean_nat_sub(v___x_3181_, v___x_3185_);
    lean_dec(v___x_3181_);
    v___x_3187_ = lean_nat_sub(v___x_3186_, v___x_3180_);
    lean_dec(v___x_3186_);
    v_h_3188_ = l_Lean_Expr_getRevArg_x21(v_e_3170_, v___x_3187_);
    if v_useSplitter_3171_ == 0 {
        let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_3178_);
        lean_dec_ref(v_inst_3177_);
        lean_dec(v_inst_3176_);
        v___x_3189_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1;
        v___x_3190_ = lean_unsigned_to_nat(0);
        v___x_3191_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0;
        lean_inc(v_toBind_3175_);
        lean_inc(v_onAlt_3174_);
        lean_inc_ref(v_resTy_3172_);
        v___f_3192_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1 as *mut core::ffi::c_void,
            10,
            9,
        );
        lean_closure_set(v___f_3192_, 0, v_u_3179_);
        lean_closure_set(v___f_3192_, 1, v_resTy_3172_);
        lean_closure_set(v___f_3192_, 2, v_c_3184_);
        lean_closure_set(v___f_3192_, 3, v_h_3188_);
        lean_closure_set(v___f_3192_, 4, v_toPure_3173_);
        lean_closure_set(v___f_3192_, 5, v_onAlt_3174_);
        lean_closure_set(v___f_3192_, 6, v___x_3180_);
        lean_closure_set(v___f_3192_, 7, v___x_3191_);
        lean_closure_set(v___f_3192_, 8, v_toBind_3175_);
        v___x_3193_ = lean_apply_4(
            v_onAlt_3174_,
            v___x_3189_,
            v_resTy_3172_,
            v___x_3190_,
            v___x_3191_,
        );
        v___x_3194_ = lean_apply_4(
            v_toBind_3175_,
            lean_box(0),
            lean_box(0),
            v___x_3193_,
            v___f_3192_,
        );
        return v___x_3194_;
    } else {
        let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
        v___x_3195_ = lean_box((v_useSplitter_3171_) as usize);
        lean_inc_n(v_toBind_3175_, 3);
        lean_inc_ref_n(v_resTy_3172_, 2);
        lean_inc(v_onAlt_3174_);
        lean_inc_n(v_inst_3176_, 2);
        v___f_3196_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed
                as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___f_3196_, 0, v___x_3180_);
        lean_closure_set(v___f_3196_, 1, v___x_3195_);
        lean_closure_set(v___f_3196_, 2, v_inst_3176_);
        lean_closure_set(v___f_3196_, 3, v_onAlt_3174_);
        lean_closure_set(v___f_3196_, 4, v_resTy_3172_);
        lean_closure_set(v___f_3196_, 5, v_toBind_3175_);
        v___x_3197_ = lean_box((v_useSplitter_3171_) as usize);
        v___f_3198_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed
                as *mut core::ffi::c_void,
            7,
            6,
        );
        lean_closure_set(v___f_3198_, 0, v___x_3180_);
        lean_closure_set(v___f_3198_, 1, v___x_3197_);
        lean_closure_set(v___f_3198_, 2, v_inst_3176_);
        lean_closure_set(v___f_3198_, 3, v_onAlt_3174_);
        lean_closure_set(v___f_3198_, 4, v_resTy_3172_);
        lean_closure_set(v___f_3198_, 5, v_toBind_3175_);
        v___f_3199_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7 as *mut core::ffi::c_void,
            11,
            10,
        );
        lean_closure_set(v___f_3199_, 0, v_u_3179_);
        lean_closure_set(v___f_3199_, 1, v_resTy_3172_);
        lean_closure_set(v___f_3199_, 2, v_c_3184_);
        lean_closure_set(v___f_3199_, 3, v_h_3188_);
        lean_closure_set(v___f_3199_, 4, v_toPure_3173_);
        lean_closure_set(v___f_3199_, 5, v_inst_3177_);
        lean_closure_set(v___f_3199_, 6, v_inst_3178_);
        lean_closure_set(v___f_3199_, 7, v___f_3198_);
        lean_closure_set(v___f_3199_, 8, v_toBind_3175_);
        lean_closure_set(v___f_3199_, 9, v___f_3196_);
        v___f_3200_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3;
        v___x_3201_ = lean_apply_2(v_inst_3176_, lean_box(0), v___f_3200_);
        v___x_3202_ = lean_apply_4(
            v_toBind_3175_,
            lean_box(0),
            lean_box(0),
            v___x_3201_,
            v___f_3199_,
        );
        return v___x_3202_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(
    mut v_e_3203_: *mut LeanObject,
    mut v_useSplitter_3204_: *mut LeanObject,
    mut v_resTy_3205_: *mut LeanObject,
    mut v_toPure_3206_: *mut LeanObject,
    mut v_onAlt_3207_: *mut LeanObject,
    mut v_toBind_3208_: *mut LeanObject,
    mut v_inst_3209_: *mut LeanObject,
    mut v_inst_3210_: *mut LeanObject,
    mut v_inst_3211_: *mut LeanObject,
    mut v_u_3212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useSplitter_boxed_3213_: u8 = 0;
    let mut v_res_3214_: *mut LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3213_ = (lean_unbox(v_useSplitter_3204_) as u8);
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
    lean_dec_ref(v_e_3203_);
    return v_res_3214_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(
    mut v___x_3215_: *mut LeanObject,
    mut v_inst_3216_: *mut LeanObject,
    mut v_____do__lift_3217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    v___x_3218_ = 0;
    v___x_3219_ = 1;
    v___x_3220_ = 1;
    v___x_3221_ = lean_box((v___x_3218_) as usize);
    v___x_3222_ = lean_box((v___x_3219_) as usize);
    v___x_3223_ = lean_box((v___x_3218_) as usize);
    v___x_3224_ = lean_box((v___x_3219_) as usize);
    v___x_3225_ = lean_box((v___x_3220_) as usize);
    v___x_3226_ = lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    lean_closure_set(v___x_3226_, 0, v___x_3215_);
    lean_closure_set(v___x_3226_, 1, v_____do__lift_3217_);
    lean_closure_set(v___x_3226_, 2, v___x_3221_);
    lean_closure_set(v___x_3226_, 3, v___x_3222_);
    lean_closure_set(v___x_3226_, 4, v___x_3223_);
    lean_closure_set(v___x_3226_, 5, v___x_3224_);
    lean_closure_set(v___x_3226_, 6, v___x_3225_);
    v___x_3227_ = lean_apply_2(v_inst_3216_, lean_box(0), v___x_3226_);
    return v___x_3227_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(
    mut v_inst_3228_: *mut LeanObject,
    mut v_onAlt_3229_: *mut LeanObject,
    mut v_resTy_3230_: *mut LeanObject,
    mut v_toBind_3231_: *mut LeanObject,
    mut v_h_3232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1;
    v___x_3234_ = lean_unsigned_to_nat(0);
    v___x_3235_ = lean_unsigned_to_nat(1);
    v___x_3236_ = lean_mk_empty_array_with_capacity(v___x_3235_);
    v___x_3237_ = lean_array_push(v___x_3236_, v_h_3232_);
    lean_inc_ref_n(v___x_3237_, 2);
    v___f_3238_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3238_, 0, v___x_3237_);
    lean_closure_set(v___f_3238_, 1, v_inst_3228_);
    v___x_3239_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3240_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3240_, 0, v___x_3237_);
    lean_ctor_set(v___x_3240_, 1, v___x_3237_);
    lean_ctor_set(v___x_3240_, 2, v___x_3239_);
    lean_ctor_set(v___x_3240_, 3, v___x_3239_);
    lean_ctor_set(v___x_3240_, 4, v___x_3239_);
    v___x_3241_ = lean_apply_4(
        v_onAlt_3229_,
        v___x_3233_,
        v_resTy_3230_,
        v___x_3234_,
        v___x_3240_,
    );
    v___x_3242_ = lean_apply_4(
        v_toBind_3231_,
        lean_box(0),
        lean_box(0),
        v___x_3241_,
        v___f_3238_,
    );
    return v___x_3242_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(
    mut v___x_3243_: *mut LeanObject,
    mut v_inst_3244_: *mut LeanObject,
    mut v_onAlt_3245_: *mut LeanObject,
    mut v_resTy_3246_: *mut LeanObject,
    mut v_toBind_3247_: *mut LeanObject,
    mut v_h_3248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    v___x_3249_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1;
    v___x_3250_ = lean_mk_empty_array_with_capacity(v___x_3243_);
    v___x_3251_ = lean_array_push(v___x_3250_, v_h_3248_);
    lean_inc_ref_n(v___x_3251_, 2);
    v___f_3252_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_3252_, 0, v___x_3251_);
    lean_closure_set(v___f_3252_, 1, v_inst_3244_);
    v___x_3253_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___closed__0;
    v___x_3254_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3254_, 0, v___x_3251_);
    lean_ctor_set(v___x_3254_, 1, v___x_3251_);
    lean_ctor_set(v___x_3254_, 2, v___x_3253_);
    lean_ctor_set(v___x_3254_, 3, v___x_3253_);
    lean_ctor_set(v___x_3254_, 4, v___x_3253_);
    v___x_3255_ = lean_apply_4(
        v_onAlt_3245_,
        v___x_3249_,
        v_resTy_3246_,
        v___x_3243_,
        v___x_3254_,
    );
    v___x_3256_ = lean_apply_4(
        v_toBind_3247_,
        lean_box(0),
        lean_box(0),
        v___x_3255_,
        v___f_3252_,
    );
    return v___x_3256_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(
    mut v_inst_3257_: *mut LeanObject,
    mut v_onAlt_3258_: *mut LeanObject,
    mut v_resTy_3259_: *mut LeanObject,
    mut v_toBind_3260_: *mut LeanObject,
    mut v_e_3261_: *mut LeanObject,
    mut v_toPure_3262_: *mut LeanObject,
    mut v_inst_3263_: *mut LeanObject,
    mut v_inst_3264_: *mut LeanObject,
    mut v___f_3265_: *mut LeanObject,
    mut v_u_3266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    v___x_3267_ = lean_unsigned_to_nat(1);
    lean_inc_n(v_toBind_3260_, 2);
    lean_inc_ref(v_resTy_3259_);
    lean_inc(v_inst_3257_);
    v___f_3268_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_3268_, 0, v___x_3267_);
    lean_closure_set(v___f_3268_, 1, v_inst_3257_);
    lean_closure_set(v___f_3268_, 2, v_onAlt_3258_);
    lean_closure_set(v___f_3268_, 3, v_resTy_3259_);
    lean_closure_set(v___f_3268_, 4, v_toBind_3260_);
    v___x_3269_ = l_Lean_Expr_getAppNumArgs(v_e_3261_);
    v___x_3270_ = lean_nat_sub(v___x_3269_, v___x_3267_);
    v___x_3271_ = lean_nat_sub(v___x_3270_, v___x_3267_);
    lean_dec(v___x_3270_);
    v_c_3272_ = l_Lean_Expr_getRevArg_x21(v_e_3261_, v___x_3271_);
    v___x_3273_ = lean_unsigned_to_nat(2);
    v___x_3274_ = lean_nat_sub(v___x_3269_, v___x_3273_);
    lean_dec(v___x_3269_);
    v___x_3275_ = lean_nat_sub(v___x_3274_, v___x_3267_);
    lean_dec(v___x_3274_);
    v_h_3276_ = l_Lean_Expr_getRevArg_x21(v_e_3261_, v___x_3275_);
    v___f_3277_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7 as *mut core::ffi::c_void,
        11,
        10,
    );
    lean_closure_set(v___f_3277_, 0, v_u_3266_);
    lean_closure_set(v___f_3277_, 1, v_resTy_3259_);
    lean_closure_set(v___f_3277_, 2, v_c_3272_);
    lean_closure_set(v___f_3277_, 3, v_h_3276_);
    lean_closure_set(v___f_3277_, 4, v_toPure_3262_);
    lean_closure_set(v___f_3277_, 5, v_inst_3263_);
    lean_closure_set(v___f_3277_, 6, v_inst_3264_);
    lean_closure_set(v___f_3277_, 7, v___f_3268_);
    lean_closure_set(v___f_3277_, 8, v_toBind_3260_);
    lean_closure_set(v___f_3277_, 9, v___f_3265_);
    v___f_3278_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3;
    v___x_3279_ = lean_apply_2(v_inst_3257_, lean_box(0), v___f_3278_);
    v___x_3280_ = lean_apply_4(
        v_toBind_3260_,
        lean_box(0),
        lean_box(0),
        v___x_3279_,
        v___f_3277_,
    );
    return v___x_3280_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(
    mut v_inst_3281_: *mut LeanObject,
    mut v_onAlt_3282_: *mut LeanObject,
    mut v_resTy_3283_: *mut LeanObject,
    mut v_toBind_3284_: *mut LeanObject,
    mut v_e_3285_: *mut LeanObject,
    mut v_toPure_3286_: *mut LeanObject,
    mut v_inst_3287_: *mut LeanObject,
    mut v_inst_3288_: *mut LeanObject,
    mut v___f_3289_: *mut LeanObject,
    mut v_u_3290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3291_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_e_3285_);
    return v_res_3291_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(
    mut v_onAlt_3292_: *mut LeanObject,
    mut v_idx_3293_: *mut LeanObject,
    mut v_expAltType_3294_: *mut LeanObject,
    mut v_altFVars_3295_: *mut LeanObject,
    mut v___alt_3296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    v___x_3297_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2;
    v___x_3298_ = lean_unsigned_to_nat(1);
    v___x_3299_ = lean_nat_add(v_idx_3293_, v___x_3298_);
    v___x_3300_ = lean_name_append_index_after(v___x_3297_, v___x_3299_);
    v___x_3301_ = lean_apply_4(
        v_onAlt_3292_,
        v___x_3300_,
        v_expAltType_3294_,
        v_idx_3293_,
        v_altFVars_3295_,
    );
    return v___x_3301_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(
    mut v_onAlt_3302_: *mut LeanObject,
    mut v_idx_3303_: *mut LeanObject,
    mut v_expAltType_3304_: *mut LeanObject,
    mut v_altFVars_3305_: *mut LeanObject,
    mut v___alt_3306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3307_: *mut LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(
        v_onAlt_3302_,
        v_idx_3303_,
        v_expAltType_3304_,
        v_altFVars_3305_,
        v___alt_3306_,
    );
    lean_dec_ref(v___alt_3306_);
    return v_res_3307_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(
    mut v_mask_3308_: *mut LeanObject,
    mut v_absMotiveBody_3309_: *mut LeanObject,
    mut v_toPure_3310_: *mut LeanObject,
    mut v_xs_3311_: *mut LeanObject,
    mut v___body_3312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    v___x_3313_ = l_Array_mask___redArg(v_mask_3308_, v_xs_3311_);
    v___x_3314_ = lean_expr_instantiate_rev(v_absMotiveBody_3309_, v___x_3313_);
    lean_dec(v___x_3313_);
    v___x_3315_ = lean_apply_2(v_toPure_3310_, lean_box(0), v___x_3314_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(
    mut v_mask_3316_: *mut LeanObject,
    mut v_absMotiveBody_3317_: *mut LeanObject,
    mut v_toPure_3318_: *mut LeanObject,
    mut v_xs_3319_: *mut LeanObject,
    mut v___body_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3321_: *mut LeanObject = core::ptr::null_mut();
    v_res_3321_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(
        v_mask_3316_,
        v_absMotiveBody_3317_,
        v_toPure_3318_,
        v_xs_3319_,
        v___body_3320_,
    );
    lean_dec_ref(v___body_3320_);
    lean_dec_ref(v_absMotiveBody_3317_);
    lean_dec_ref(v_mask_3316_);
    return v_res_3321_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(
    mut v_toFunctor_3322_: *mut LeanObject,
    mut v_mask_3323_: *mut LeanObject,
    mut v_toPure_3324_: *mut LeanObject,
    mut v_inst_3325_: *mut LeanObject,
    mut v_inst_3326_: *mut LeanObject,
    mut v_inst_3327_: *mut LeanObject,
    mut v_inst_3328_: *mut LeanObject,
    mut v_inst_3329_: *mut LeanObject,
    mut v_matcherApp_3330_: *mut LeanObject,
    mut v_useSplitter_3331_: u8,
    mut v___f_3332_: *mut LeanObject,
    mut v___f_3333_: *mut LeanObject,
    mut v_absMotiveBody_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    v_map_3335_ = lean_ctor_get(v_toFunctor_3322_, 0);
    lean_inc(v_map_3335_);
    lean_dec_ref(v_toFunctor_3322_);
    lean_inc(v_toPure_3324_);
    v___f_3336_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_3336_, 0, v_mask_3323_);
    lean_closure_set(v___f_3336_, 1, v_absMotiveBody_3334_);
    lean_closure_set(v___f_3336_, 2, v_toPure_3324_);
    v___x_3337_ = lean_apply_1(v_toPure_3324_, lean_box(0));
    lean_inc(v___x_3337_);
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
    v___x_3339_ = lean_apply_4(
        v_map_3335_,
        lean_box(0),
        lean_box(0),
        v___f_3333_,
        v___x_3338_,
    );
    return v___x_3339_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(
    mut v_toFunctor_3340_: *mut LeanObject,
    mut v_mask_3341_: *mut LeanObject,
    mut v_toPure_3342_: *mut LeanObject,
    mut v_inst_3343_: *mut LeanObject,
    mut v_inst_3344_: *mut LeanObject,
    mut v_inst_3345_: *mut LeanObject,
    mut v_inst_3346_: *mut LeanObject,
    mut v_inst_3347_: *mut LeanObject,
    mut v_matcherApp_3348_: *mut LeanObject,
    mut v_useSplitter_3349_: *mut LeanObject,
    mut v___f_3350_: *mut LeanObject,
    mut v___f_3351_: *mut LeanObject,
    mut v_absMotiveBody_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useSplitter_boxed_3353_: u8 = 0;
    let mut v_res_3354_: *mut LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3353_ = (lean_unbox(v_useSplitter_3349_) as u8);
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
    mut v_inst_3357_: *mut LeanObject,
    mut v_inst_3358_: *mut LeanObject,
    mut v_inst_3359_: *mut LeanObject,
    mut v_inst_3360_: *mut LeanObject,
    mut v_inst_3361_: *mut LeanObject,
    mut v_info_3362_: *mut LeanObject,
    mut v_resTy_3363_: *mut LeanObject,
    mut v_onAlt_3364_: *mut LeanObject,
    mut v_useSplitter_3365_: u8,
) -> *mut LeanObject {
    match lean_obj_tag(v_info_3362_) {
        0 => {
            let mut v_toApplicative_3366_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_3367_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3368_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_3369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3371_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_3366_ = lean_ctor_get(v_inst_3359_, 0);
            lean_dec_ref(v_inst_3361_);
            lean_dec_ref(v_inst_3360_);
            v_toBind_3367_ = lean_ctor_get(v_inst_3359_, 1);
            lean_inc_n(v_toBind_3367_, 2);
            v_toPure_3368_ = lean_ctor_get(v_toApplicative_3366_, 1);
            lean_inc(v_toPure_3368_);
            v_e_3369_ = lean_ctor_get(v_info_3362_, 0);
            lean_inc_ref(v_e_3369_);
            lean_dec_ref_known(v_info_3362_, 1);
            v___x_3370_ = lean_box((v_useSplitter_3365_) as usize);
            lean_inc(v_inst_3357_);
            lean_inc_ref(v_resTy_3363_);
            v___f_3371_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_3371_, 0, v_e_3369_);
            lean_closure_set(v___f_3371_, 1, v___x_3370_);
            lean_closure_set(v___f_3371_, 2, v_resTy_3363_);
            lean_closure_set(v___f_3371_, 3, v_toPure_3368_);
            lean_closure_set(v___f_3371_, 4, v_onAlt_3364_);
            lean_closure_set(v___f_3371_, 5, v_toBind_3367_);
            lean_closure_set(v___f_3371_, 6, v_inst_3357_);
            lean_closure_set(v___f_3371_, 7, v_inst_3358_);
            lean_closure_set(v___f_3371_, 8, v_inst_3359_);
            v___x_3372_ =
                lean_alloc_closure(l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void, 6, 1);
            lean_closure_set(v___x_3372_, 0, v_resTy_3363_);
            v___x_3373_ = lean_apply_2(v_inst_3357_, lean_box(0), v___x_3372_);
            v___x_3374_ = lean_apply_4(
                v_toBind_3367_,
                lean_box(0),
                lean_box(0),
                v___x_3373_,
                v___f_3371_,
            );
            return v___x_3374_;
        }
        1 => {
            let mut v_toApplicative_3375_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_3376_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3377_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_3378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3379_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3380_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_3375_ = lean_ctor_get(v_inst_3359_, 0);
            lean_dec_ref(v_inst_3361_);
            lean_dec_ref(v_inst_3360_);
            v_toBind_3376_ = lean_ctor_get(v_inst_3359_, 1);
            lean_inc_n(v_toBind_3376_, 3);
            v_toPure_3377_ = lean_ctor_get(v_toApplicative_3375_, 1);
            lean_inc(v_toPure_3377_);
            v_e_3378_ = lean_ctor_get(v_info_3362_, 0);
            lean_inc_ref(v_e_3378_);
            lean_dec_ref_known(v_info_3362_, 1);
            lean_inc_ref_n(v_resTy_3363_, 2);
            lean_inc(v_onAlt_3364_);
            lean_inc_n(v_inst_3357_, 2);
            v___f_3379_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11
                    as *mut core::ffi::c_void,
                5,
                4,
            );
            lean_closure_set(v___f_3379_, 0, v_inst_3357_);
            lean_closure_set(v___f_3379_, 1, v_onAlt_3364_);
            lean_closure_set(v___f_3379_, 2, v_resTy_3363_);
            lean_closure_set(v___f_3379_, 3, v_toBind_3376_);
            v___f_3380_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed
                    as *mut core::ffi::c_void,
                10,
                9,
            );
            lean_closure_set(v___f_3380_, 0, v_inst_3357_);
            lean_closure_set(v___f_3380_, 1, v_onAlt_3364_);
            lean_closure_set(v___f_3380_, 2, v_resTy_3363_);
            lean_closure_set(v___f_3380_, 3, v_toBind_3376_);
            lean_closure_set(v___f_3380_, 4, v_e_3378_);
            lean_closure_set(v___f_3380_, 5, v_toPure_3377_);
            lean_closure_set(v___f_3380_, 6, v_inst_3358_);
            lean_closure_set(v___f_3380_, 7, v_inst_3359_);
            lean_closure_set(v___f_3380_, 8, v___f_3379_);
            v___x_3381_ =
                lean_alloc_closure(l_Lean_Meta_getLevel___boxed as *mut core::ffi::c_void, 6, 1);
            lean_closure_set(v___x_3381_, 0, v_resTy_3363_);
            v___x_3382_ = lean_apply_2(v_inst_3357_, lean_box(0), v___x_3381_);
            v___x_3383_ = lean_apply_4(
                v_toBind_3376_,
                lean_box(0),
                lean_box(0),
                v___x_3382_,
                v___f_3380_,
            );
            return v___x_3383_;
        }
        _ => {
            let mut v_toApplicative_3384_: *mut LeanObject = core::ptr::null_mut();
            let mut v_matcherApp_3385_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_3386_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toFunctor_3387_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3388_: *mut LeanObject = core::ptr::null_mut();
            let mut v_discrs_3389_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3390_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3391_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3392_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
            let mut v_sz_3394_: usize = 0;
            let mut v___x_3395_: usize = 0;
            let mut v_mask_3396_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_3398_: *mut LeanObject = core::ptr::null_mut();
            let mut v_maskedDiscrs_3399_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
            v_toApplicative_3384_ = lean_ctor_get(v_inst_3359_, 0);
            v_matcherApp_3385_ = lean_ctor_get(v_info_3362_, 0);
            lean_inc_ref(v_matcherApp_3385_);
            lean_dec_ref_known(v_info_3362_, 1);
            v_toBind_3386_ = lean_ctor_get(v_inst_3359_, 1);
            lean_inc(v_toBind_3386_);
            v_toFunctor_3387_ = lean_ctor_get(v_toApplicative_3384_, 0);
            lean_inc_ref(v_toFunctor_3387_);
            v_toPure_3388_ = lean_ctor_get(v_toApplicative_3384_, 1);
            lean_inc(v_toPure_3388_);
            v_discrs_3389_ = lean_ctor_get(v_matcherApp_3385_, 5);
            lean_inc_ref_n(v_discrs_3389_, 2);
            v___f_3390_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0;
            v___f_3391_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed
                    as *mut core::ffi::c_void,
                5,
                1,
            );
            lean_closure_set(v___f_3391_, 0, v_onAlt_3364_);
            v___f_3392_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__1;
            v___x_3393_ =
                l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__9;
            v_sz_3394_ = lean_array_size(v_discrs_3389_);
            v___x_3395_ = 0usize;
            v_mask_3396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_3393_,
                v___f_3392_,
                v_sz_3394_,
                v___x_3395_,
                v_discrs_3389_,
            );
            v___x_3397_ = lean_box((v_useSplitter_3365_) as usize);
            lean_inc(v_inst_3357_);
            lean_inc(v_mask_3396_);
            v___f_3398_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed
                    as *mut core::ffi::c_void,
                13,
                12,
            );
            lean_closure_set(v___f_3398_, 0, v_toFunctor_3387_);
            lean_closure_set(v___f_3398_, 1, v_mask_3396_);
            lean_closure_set(v___f_3398_, 2, v_toPure_3388_);
            lean_closure_set(v___f_3398_, 3, v_inst_3357_);
            lean_closure_set(v___f_3398_, 4, v_inst_3358_);
            lean_closure_set(v___f_3398_, 5, v_inst_3359_);
            lean_closure_set(v___f_3398_, 6, v_inst_3360_);
            lean_closure_set(v___f_3398_, 7, v_inst_3361_);
            lean_closure_set(v___f_3398_, 8, v_matcherApp_3385_);
            lean_closure_set(v___f_3398_, 9, v___x_3397_);
            lean_closure_set(v___f_3398_, 10, v___f_3391_);
            lean_closure_set(v___f_3398_, 11, v___f_3390_);
            v_maskedDiscrs_3399_ = l_Array_mask___redArg(v_mask_3396_, v_discrs_3389_);
            lean_dec(v_mask_3396_);
            v___x_3400_ = lean_alloc_closure(
                l_Lean_Expr_abstractM___boxed as *mut core::ffi::c_void,
                7,
                2,
            );
            lean_closure_set(v___x_3400_, 0, v_resTy_3363_);
            lean_closure_set(v___x_3400_, 1, v_maskedDiscrs_3399_);
            v___x_3401_ = lean_apply_2(v_inst_3357_, lean_box(0), v___x_3400_);
            v___x_3402_ = lean_apply_4(
                v_toBind_3386_,
                lean_box(0),
                lean_box(0),
                v___x_3401_,
                v___f_3398_,
            );
            return v___x_3402_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(
    mut v_inst_3403_: *mut LeanObject,
    mut v_inst_3404_: *mut LeanObject,
    mut v_inst_3405_: *mut LeanObject,
    mut v_inst_3406_: *mut LeanObject,
    mut v_inst_3407_: *mut LeanObject,
    mut v_info_3408_: *mut LeanObject,
    mut v_resTy_3409_: *mut LeanObject,
    mut v_onAlt_3410_: *mut LeanObject,
    mut v_useSplitter_3411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useSplitter_boxed_3412_: u8 = 0;
    let mut v_res_3413_: *mut LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3412_ = (lean_unbox(v_useSplitter_3411_) as u8);
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
    mut v_n_3414_: *mut LeanObject,
    mut v_inst_3415_: *mut LeanObject,
    mut v_inst_3416_: *mut LeanObject,
    mut v_inst_3417_: *mut LeanObject,
    mut v_inst_3418_: *mut LeanObject,
    mut v_inst_3419_: *mut LeanObject,
    mut v_inst_3420_: *mut LeanObject,
    mut v_inst_3421_: *mut LeanObject,
    mut v_inst_3422_: *mut LeanObject,
    mut v_info_3423_: *mut LeanObject,
    mut v_resTy_3424_: *mut LeanObject,
    mut v_onAlt_3425_: *mut LeanObject,
    mut v_useSplitter_3426_: u8,
) -> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_3428_: *mut LeanObject,
    mut v_inst_3429_: *mut LeanObject,
    mut v_inst_3430_: *mut LeanObject,
    mut v_inst_3431_: *mut LeanObject,
    mut v_inst_3432_: *mut LeanObject,
    mut v_inst_3433_: *mut LeanObject,
    mut v_inst_3434_: *mut LeanObject,
    mut v_inst_3435_: *mut LeanObject,
    mut v_inst_3436_: *mut LeanObject,
    mut v_info_3437_: *mut LeanObject,
    mut v_resTy_3438_: *mut LeanObject,
    mut v_onAlt_3439_: *mut LeanObject,
    mut v_useSplitter_3440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_useSplitter_boxed_3441_: u8 = 0;
    let mut v_res_3442_: *mut LeanObject = core::ptr::null_mut();
    v_useSplitter_boxed_3441_ = (lean_unbox(v_useSplitter_3440_) as u8);
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
    lean_dec(v_inst_3436_);
    lean_dec(v_inst_3435_);
    lean_dec_ref(v_inst_3434_);
    return v_res_3442_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(
    mut v_info_3443_: *mut LeanObject,
    mut v_e_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_info_3443_) == 2 {
        let mut v_matcherApp_3453_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toMatcherInfo_3454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
        v_matcherApp_3453_ = lean_ctor_get(v_info_3443_, 0);
        lean_inc_ref(v_matcherApp_3453_);
        lean_dec_ref_known(v_info_3443_, 1);
        v_toMatcherInfo_3454_ = lean_ctor_get(v_matcherApp_3453_, 0);
        lean_inc_ref(v_toMatcherInfo_3454_);
        lean_dec_ref(v_matcherApp_3453_);
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
        let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_3444_);
        lean_dec_ref(v_info_3443_);
        v___x_3456_ = lean_box(0);
        v___x_3457_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3457_, 0, v___x_3456_);
        return v___x_3457_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(
    mut v_info_3458_: *mut LeanObject,
    mut v_e_3459_: *mut LeanObject,
    mut v_a_3460_: *mut LeanObject,
    mut v_a_3461_: *mut LeanObject,
    mut v_a_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
    mut v_a_3464_: *mut LeanObject,
    mut v_a_3465_: *mut LeanObject,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3466_);
    lean_dec_ref(v_a_3465_);
    lean_dec(v_a_3464_);
    lean_dec_ref(v_a_3463_);
    lean_dec(v_a_3462_);
    lean_dec_ref(v_a_3461_);
    lean_dec(v_a_3460_);
    return v_res_3468_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(
    mut v_declName_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    v___x_3472_ = lean_st_ref_get(v___y_3470_);
    v_env_3473_ = lean_ctor_get(v___x_3472_, 0);
    lean_inc_ref(v_env_3473_);
    lean_dec(v___x_3472_);
    v___x_3474_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3473_, v_declName_3469_);
    v___x_3475_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3475_, 0, v___x_3474_);
    return v___x_3475_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(
    mut v_declName_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3479_: *mut LeanObject = core::ptr::null_mut();
    v_res_3479_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_3476_, v___y_3477_);
    lean_dec(v___y_3477_);
    return v_res_3479_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(
    mut v_msgData_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    v___x_3486_ = lean_st_ref_get(v___y_3484_);
    v_env_3487_ = lean_ctor_get(v___x_3486_, 0);
    lean_inc_ref(v_env_3487_);
    lean_dec(v___x_3486_);
    v___x_3488_ = lean_st_ref_get(v___y_3482_);
    v_mctx_3489_ = lean_ctor_get(v___x_3488_, 0);
    lean_inc_ref(v_mctx_3489_);
    lean_dec(v___x_3488_);
    v_lctx_3490_ = lean_ctor_get(v___y_3481_, 2);
    v_options_3491_ = lean_ctor_get(v___y_3483_, 2);
    lean_inc_ref(v_options_3491_);
    lean_inc_ref(v_lctx_3490_);
    v___x_3492_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3492_, 0, v_env_3487_);
    lean_ctor_set(v___x_3492_, 1, v_mctx_3489_);
    lean_ctor_set(v___x_3492_, 2, v_lctx_3490_);
    lean_ctor_set(v___x_3492_, 3, v_options_3491_);
    v___x_3493_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3493_, 0, v___x_3492_);
    lean_ctor_set(v___x_3493_, 1, v_msgData_3480_);
    v___x_3494_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3494_, 0, v___x_3493_);
    return v___x_3494_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(
    mut v_msgData_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
    mut v___y_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3501_: *mut LeanObject = core::ptr::null_mut();
    v_res_3501_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
    lean_dec(v___y_3499_);
    lean_dec_ref(v___y_3498_);
    lean_dec(v___y_3497_);
    lean_dec_ref(v___y_3496_);
    return v_res_3501_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(
    mut v_msg_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
    mut v___y_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3508_ = lean_ctor_get(v___y_3505_, 5);
                v___x_3509_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
                v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
                v_isSharedCheck_3518_ = (!lean_is_exclusive(v___x_3509_)) as u8;
                if v_isSharedCheck_3518_ == 0 {
                    v___x_3512_ = v___x_3509_;
                    v_isShared_3513_ = v_isSharedCheck_3518_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3510_);
                    lean_dec(v___x_3509_);
                    v___x_3512_ = lean_box(0);
                    v_isShared_3513_ = v_isSharedCheck_3518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3508_);
                v___x_3514_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3514_, 0, v_ref_3508_);
                lean_ctor_set(v___x_3514_, 1, v_a_3510_);
                if v_isShared_3513_ == 0 {
                    lean_ctor_set_tag(v___x_3512_, 1);
                    lean_ctor_set(v___x_3512_, 0, v___x_3514_);
                    v___x_3516_ = v___x_3512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
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
    mut v_msg_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3525_: *mut LeanObject = core::ptr::null_mut();
    v_res_3525_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
    lean_dec(v___y_3523_);
    lean_dec_ref(v___y_3522_);
    lean_dec(v___y_3521_);
    lean_dec_ref(v___y_3520_);
    return v_res_3525_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(
    mut v_ref_3526_: *mut LeanObject,
    mut v_msg_3527_: *mut LeanObject,
    mut v___y_3528_: *mut LeanObject,
    mut v___y_3529_: *mut LeanObject,
    mut v___y_3530_: *mut LeanObject,
    mut v___y_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3545_: u8 = 0;
    let mut v_cancelTk_x3f_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3547_: u8 = 0;
    let mut v_inheritedTraceOptions_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3533_ = lean_ctor_get(v___y_3530_, 0);
    v_fileMap_3534_ = lean_ctor_get(v___y_3530_, 1);
    v_options_3535_ = lean_ctor_get(v___y_3530_, 2);
    v_currRecDepth_3536_ = lean_ctor_get(v___y_3530_, 3);
    v_maxRecDepth_3537_ = lean_ctor_get(v___y_3530_, 4);
    v_ref_3538_ = lean_ctor_get(v___y_3530_, 5);
    v_currNamespace_3539_ = lean_ctor_get(v___y_3530_, 6);
    v_openDecls_3540_ = lean_ctor_get(v___y_3530_, 7);
    v_initHeartbeats_3541_ = lean_ctor_get(v___y_3530_, 8);
    v_maxHeartbeats_3542_ = lean_ctor_get(v___y_3530_, 9);
    v_quotContext_3543_ = lean_ctor_get(v___y_3530_, 10);
    v_currMacroScope_3544_ = lean_ctor_get(v___y_3530_, 11);
    v_diag_3545_ = lean_ctor_get_uint8(
        v___y_3530_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3546_ = lean_ctor_get(v___y_3530_, 12);
    v_suppressElabErrors_3547_ = lean_ctor_get_uint8(
        v___y_3530_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3548_ = lean_ctor_get(v___y_3530_, 13);
    v_ref_3549_ = l_Lean_replaceRef(v_ref_3526_, v_ref_3538_);
    lean_inc_ref(v_inheritedTraceOptions_3548_);
    lean_inc(v_cancelTk_x3f_3546_);
    lean_inc(v_currMacroScope_3544_);
    lean_inc(v_quotContext_3543_);
    lean_inc(v_maxHeartbeats_3542_);
    lean_inc(v_initHeartbeats_3541_);
    lean_inc(v_openDecls_3540_);
    lean_inc(v_currNamespace_3539_);
    lean_inc(v_maxRecDepth_3537_);
    lean_inc(v_currRecDepth_3536_);
    lean_inc_ref(v_options_3535_);
    lean_inc_ref(v_fileMap_3534_);
    lean_inc_ref(v_fileName_3533_);
    v___x_3550_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3550_, 0, v_fileName_3533_);
    lean_ctor_set(v___x_3550_, 1, v_fileMap_3534_);
    lean_ctor_set(v___x_3550_, 2, v_options_3535_);
    lean_ctor_set(v___x_3550_, 3, v_currRecDepth_3536_);
    lean_ctor_set(v___x_3550_, 4, v_maxRecDepth_3537_);
    lean_ctor_set(v___x_3550_, 5, v_ref_3549_);
    lean_ctor_set(v___x_3550_, 6, v_currNamespace_3539_);
    lean_ctor_set(v___x_3550_, 7, v_openDecls_3540_);
    lean_ctor_set(v___x_3550_, 8, v_initHeartbeats_3541_);
    lean_ctor_set(v___x_3550_, 9, v_maxHeartbeats_3542_);
    lean_ctor_set(v___x_3550_, 10, v_quotContext_3543_);
    lean_ctor_set(v___x_3550_, 11, v_currMacroScope_3544_);
    lean_ctor_set(v___x_3550_, 12, v_cancelTk_x3f_3546_);
    lean_ctor_set(v___x_3550_, 13, v_inheritedTraceOptions_3548_);
    lean_ctor_set_uint8(
        v___x_3550_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3545_,
    );
    lean_ctor_set_uint8(
        v___x_3550_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3547_,
    );
    v___x_3551_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_3527_, v___y_3528_, v___y_3529_, v___x_3550_, v___y_3531_);
    lean_dec_ref_known(v___x_3550_, 14);
    return v___x_3551_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_ref_3552_: *mut LeanObject,
    mut v_msg_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3559_: *mut LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_3552_, v_msg_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
    lean_dec(v___y_3557_);
    lean_dec_ref(v___y_3556_);
    lean_dec(v___y_3555_);
    lean_dec_ref(v___y_3554_);
    lean_dec(v_ref_3552_);
    return v_res_3559_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    v___x_3560_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3560_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    v___x_3561_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
    v___x_3562_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3562_, 0, v___x_3561_);
    return v___x_3562_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    v___x_3563_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_3564_ = lean_unsigned_to_nat(0);
    v___x_3565_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3565_, 0, v___x_3564_);
    lean_ctor_set(v___x_3565_, 1, v___x_3564_);
    lean_ctor_set(v___x_3565_, 2, v___x_3564_);
    lean_ctor_set(v___x_3565_, 3, v___x_3564_);
    lean_ctor_set(v___x_3565_, 4, v___x_3563_);
    lean_ctor_set(v___x_3565_, 5, v___x_3563_);
    lean_ctor_set(v___x_3565_, 6, v___x_3563_);
    lean_ctor_set(v___x_3565_, 7, v___x_3563_);
    lean_ctor_set(v___x_3565_, 8, v___x_3563_);
    lean_ctor_set(v___x_3565_, 9, v___x_3563_);
    return v___x_3565_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    v___x_3566_ = lean_unsigned_to_nat(32);
    v___x_3567_ = lean_mk_empty_array_with_capacity(v___x_3566_);
    v___x_3568_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3568_, 0, v___x_3567_);
    return v___x_3568_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3569_: usize = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    v___x_3569_ = 5usize;
    v___x_3570_ = lean_unsigned_to_nat(0);
    v___x_3571_ = lean_unsigned_to_nat(32);
    v___x_3572_ = lean_mk_empty_array_with_capacity(v___x_3571_);
    v___x_3573_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
    v___x_3574_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3574_, 0, v___x_3573_);
    lean_ctor_set(v___x_3574_, 1, v___x_3572_);
    lean_ctor_set(v___x_3574_, 2, v___x_3570_);
    lean_ctor_set(v___x_3574_, 3, v___x_3570_);
    lean_ctor_set_usize(v___x_3574_, 4, v___x_3569_);
    return v___x_3574_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    v___x_3575_ = lean_box(1);
    v___x_3576_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
    v___x_3577_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_3578_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3578_, 0, v___x_3577_);
    lean_ctor_set(v___x_3578_, 1, v___x_3576_);
    lean_ctor_set(v___x_3578_, 2, v___x_3575_);
    return v___x_3578_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    v___x_3580_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6;
    v___x_3581_ = l_Lean_stringToMessageData(v___x_3580_);
    return v___x_3581_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    v___x_3583_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8;
    v___x_3584_ = l_Lean_stringToMessageData(v___x_3583_);
    return v___x_3584_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10;
    v___x_3587_ = l_Lean_stringToMessageData(v___x_3586_);
    return v___x_3587_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    v___x_3589_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12;
    v___x_3590_ = l_Lean_stringToMessageData(v___x_3589_);
    return v___x_3590_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    v___x_3592_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14;
    v___x_3593_ = l_Lean_stringToMessageData(v___x_3592_);
    return v___x_3593_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3595_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16;
    v___x_3596_ = l_Lean_stringToMessageData(v___x_3595_);
    return v___x_3596_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18;
    v___x_3599_ = l_Lean_stringToMessageData(v___x_3598_);
    return v___x_3599_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(
    mut v_msg_3600_: *mut LeanObject,
    mut v_declHint_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: u8 = 0;
    let mut v_isExporting_3607_: u8 = 0;
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: u8 = 0;
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: u8 = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3604_ = lean_st_ref_get(v___y_3602_);
                v_env_3605_ = lean_ctor_get(v___x_3604_, 0);
                lean_inc_ref(v_env_3605_);
                lean_dec(v___x_3604_);
                v___x_3606_ = l_Lean_Name_isAnonymous(v_declHint_3601_);
                if v___x_3606_ == 0 {
                    v_isExporting_3607_ = lean_ctor_get_uint8(
                        v_env_3605_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3607_ == 0 {
                        lean_dec_ref(v_env_3605_);
                        lean_dec(v_declHint_3601_);
                        v___x_3608_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3608_, 0, v_msg_3600_);
                        return v___x_3608_;
                    } else {
                        lean_inc_ref(v_env_3605_);
                        v___x_3609_ = l_Lean_Environment_setExporting(v_env_3605_, v___x_3606_);
                        lean_inc(v_declHint_3601_);
                        lean_inc_ref(v___x_3609_);
                        v___x_3610_ = l_Lean_Environment_contains(
                            v___x_3609_,
                            v_declHint_3601_,
                            v_isExporting_3607_,
                        );
                        if v___x_3610_ == 0 {
                            lean_dec_ref(v___x_3609_);
                            lean_dec_ref(v_env_3605_);
                            lean_dec(v_declHint_3601_);
                            v___x_3611_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3611_, 0, v_msg_3600_);
                            return v___x_3611_;
                        } else {
                            v___x_3612_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
                            v___x_3613_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
                            v___x_3614_ = l_Lean_Options_empty;
                            v___x_3615_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3615_, 0, v___x_3609_);
                            lean_ctor_set(v___x_3615_, 1, v___x_3612_);
                            lean_ctor_set(v___x_3615_, 2, v___x_3613_);
                            lean_ctor_set(v___x_3615_, 3, v___x_3614_);
                            lean_inc(v_declHint_3601_);
                            v___x_3616_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3601_, v___x_3606_);
                            v_c_3617_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3617_, 0, v___x_3615_);
                            lean_ctor_set(v_c_3617_, 1, v___x_3616_);
                            v___x_3618_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3605_,
                                v_declHint_3601_,
                            );
                            if lean_obj_tag(v___x_3618_) == 0 {
                                lean_dec_ref(v_env_3605_);
                                lean_dec(v_declHint_3601_);
                                v___x_3619_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
                                v___x_3620_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3620_, 0, v___x_3619_);
                                lean_ctor_set(v___x_3620_, 1, v_c_3617_);
                                v___x_3621_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
                                v___x_3622_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3622_, 0, v___x_3620_);
                                lean_ctor_set(v___x_3622_, 1, v___x_3621_);
                                v___x_3623_ = l_Lean_MessageData_note(v___x_3622_);
                                v___x_3624_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3624_, 0, v_msg_3600_);
                                lean_ctor_set(v___x_3624_, 1, v___x_3623_);
                                v___x_3625_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3625_, 0, v___x_3624_);
                                return v___x_3625_;
                            } else {
                                v_val_3626_ = lean_ctor_get(v___x_3618_, 0);
                                v_isSharedCheck_3661_ = (!lean_is_exclusive(v___x_3618_)) as u8;
                                if v_isSharedCheck_3661_ == 0 {
                                    v___x_3628_ = v___x_3618_;
                                    v_isShared_3629_ = v_isSharedCheck_3661_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3626_);
                                    lean_dec(v___x_3618_);
                                    v___x_3628_ = lean_box(0);
                                    v_isShared_3629_ = v_isSharedCheck_3661_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3605_);
                    lean_dec(v_declHint_3601_);
                    v___x_3662_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3662_, 0, v_msg_3600_);
                    return v___x_3662_;
                }
            }
            1 => {
                v___x_3630_ = lean_box(0);
                v___x_3631_ = l_Lean_Environment_header(v_env_3605_);
                lean_dec_ref(v_env_3605_);
                v___x_3632_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3631_);
                v_mod_3633_ = lean_array_get(v___x_3630_, v___x_3632_, v_val_3626_);
                lean_dec(v_val_3626_);
                lean_dec_ref(v___x_3632_);
                v___x_3634_ = l_Lean_isPrivateName(v_declHint_3601_);
                lean_dec(v_declHint_3601_);
                if v___x_3634_ == 0 {
                    v___x_3635_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
                    v___x_3636_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3636_, 0, v___x_3635_);
                    lean_ctor_set(v___x_3636_, 1, v_c_3617_);
                    v___x_3637_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
                    v___x_3638_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3638_, 0, v___x_3636_);
                    lean_ctor_set(v___x_3638_, 1, v___x_3637_);
                    v___x_3639_ = l_Lean_MessageData_ofName(v_mod_3633_);
                    v___x_3640_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3640_, 0, v___x_3638_);
                    lean_ctor_set(v___x_3640_, 1, v___x_3639_);
                    v___x_3641_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
                    v___x_3642_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3642_, 0, v___x_3640_);
                    lean_ctor_set(v___x_3642_, 1, v___x_3641_);
                    v___x_3643_ = l_Lean_MessageData_note(v___x_3642_);
                    v___x_3644_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3644_, 0, v_msg_3600_);
                    lean_ctor_set(v___x_3644_, 1, v___x_3643_);
                    if v_isShared_3629_ == 0 {
                        lean_ctor_set_tag(v___x_3628_, 0);
                        lean_ctor_set(v___x_3628_, 0, v___x_3644_);
                        v___x_3646_ = v___x_3628_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3647_, 0, v___x_3644_);
                        v___x_3646_ = v_reuseFailAlloc_3647_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3648_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
                    v___x_3649_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3649_, 0, v___x_3648_);
                    lean_ctor_set(v___x_3649_, 1, v_c_3617_);
                    v___x_3650_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
                    v___x_3651_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3651_, 0, v___x_3649_);
                    lean_ctor_set(v___x_3651_, 1, v___x_3650_);
                    v___x_3652_ = l_Lean_MessageData_ofName(v_mod_3633_);
                    v___x_3653_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3653_, 0, v___x_3651_);
                    lean_ctor_set(v___x_3653_, 1, v___x_3652_);
                    v___x_3654_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
                    v___x_3655_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3655_, 0, v___x_3653_);
                    lean_ctor_set(v___x_3655_, 1, v___x_3654_);
                    v___x_3656_ = l_Lean_MessageData_note(v___x_3655_);
                    v___x_3657_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3657_, 0, v_msg_3600_);
                    lean_ctor_set(v___x_3657_, 1, v___x_3656_);
                    if v_isShared_3629_ == 0 {
                        lean_ctor_set_tag(v___x_3628_, 0);
                        lean_ctor_set(v___x_3628_, 0, v___x_3657_);
                        v___x_3659_ = v___x_3628_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3657_);
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
    mut v_msg_3663_: *mut LeanObject,
    mut v_declHint_3664_: *mut LeanObject,
    mut v___y_3665_: *mut LeanObject,
    mut v___y_3666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3667_: *mut LeanObject = core::ptr::null_mut();
    v_res_3667_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_3663_, v_declHint_3664_, v___y_3665_);
    lean_dec(v___y_3665_);
    return v_res_3667_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(
    mut v_msg_3668_: *mut LeanObject,
    mut v_declHint_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
    mut v___y_3671_: *mut LeanObject,
    mut v___y_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3679_: u8 = 0;
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3675_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_3668_, v_declHint_3669_, v___y_3673_);
                v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
                v_isSharedCheck_3685_ = (!lean_is_exclusive(v___x_3675_)) as u8;
                if v_isSharedCheck_3685_ == 0 {
                    v___x_3678_ = v___x_3675_;
                    v_isShared_3679_ = v_isSharedCheck_3685_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3676_);
                    lean_dec(v___x_3675_);
                    v___x_3678_ = lean_box(0);
                    v_isShared_3679_ = v_isSharedCheck_3685_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3680_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3681_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3681_, 0, v___x_3680_);
                lean_ctor_set(v___x_3681_, 1, v_a_3676_);
                if v_isShared_3679_ == 0 {
                    lean_ctor_set(v___x_3678_, 0, v___x_3681_);
                    v___x_3683_ = v___x_3678_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
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
    mut v_msg_3686_: *mut LeanObject,
    mut v_declHint_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3693_: *mut LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_3686_, v_declHint_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
    lean_dec(v___y_3691_);
    lean_dec_ref(v___y_3690_);
    lean_dec(v___y_3689_);
    lean_dec_ref(v___y_3688_);
    return v_res_3693_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_3694_: *mut LeanObject,
    mut v_msg_3695_: *mut LeanObject,
    mut v_declHint_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
    mut v___y_3699_: *mut LeanObject,
    mut v___y_3700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    v___x_3702_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_3695_, v_declHint_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
    v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
    lean_inc(v_a_3703_);
    lean_dec_ref(v___x_3702_);
    v___x_3704_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_3694_, v_a_3703_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
    return v___x_3704_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_3705_: *mut LeanObject,
    mut v_msg_3706_: *mut LeanObject,
    mut v_declHint_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
    mut v___y_3709_: *mut LeanObject,
    mut v___y_3710_: *mut LeanObject,
    mut v___y_3711_: *mut LeanObject,
    mut v___y_3712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3713_: *mut LeanObject = core::ptr::null_mut();
    v_res_3713_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3705_, v_msg_3706_, v_declHint_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
    lean_dec(v___y_3711_);
    lean_dec_ref(v___y_3710_);
    lean_dec(v___y_3709_);
    lean_dec_ref(v___y_3708_);
    lean_dec(v_ref_3705_);
    return v_res_3713_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    v___x_3715_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0;
    v___x_3716_ = l_Lean_stringToMessageData(v___x_3715_);
    return v___x_3716_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    v___x_3718_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2;
    v___x_3719_ = l_Lean_stringToMessageData(v___x_3718_);
    return v___x_3719_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_3720_: *mut LeanObject,
    mut v_constName_3721_: *mut LeanObject,
    mut v___y_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: u8 = 0;
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    v___x_3727_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
    v___x_3728_ = 0;
    lean_inc(v_constName_3721_);
    v___x_3729_ = l_Lean_MessageData_ofConstName(v_constName_3721_, v___x_3728_);
    v___x_3730_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3730_, 0, v___x_3727_);
    lean_ctor_set(v___x_3730_, 1, v___x_3729_);
    v___x_3731_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
    v___x_3732_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3732_, 0, v___x_3730_);
    lean_ctor_set(v___x_3732_, 1, v___x_3731_);
    v___x_3733_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_3720_, v___x_3732_, v_constName_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
    return v___x_3733_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_3734_: *mut LeanObject,
    mut v_constName_3735_: *mut LeanObject,
    mut v___y_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
    mut v___y_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3741_: *mut LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3734_, v_constName_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
    lean_dec(v___y_3739_);
    lean_dec_ref(v___y_3738_);
    lean_dec(v___y_3737_);
    lean_dec_ref(v___y_3736_);
    lean_dec(v_ref_3734_);
    return v_res_3741_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_constName_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
    mut v___y_3744_: *mut LeanObject,
    mut v___y_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3748_ = lean_ctor_get(v___y_3745_, 5);
    v___x_3749_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_3748_, v_constName_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
    return v___x_3749_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_3750_: *mut LeanObject,
    mut v___y_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3756_: *mut LeanObject = core::ptr::null_mut();
    v_res_3756_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
    lean_dec(v___y_3754_);
    lean_dec_ref(v___y_3753_);
    lean_dec(v___y_3752_);
    lean_dec_ref(v___y_3751_);
    return v_res_3756_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(
    mut v_constName_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
    mut v___y_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: u8 = 0;
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3763_ = lean_st_ref_get(v___y_3761_);
                v_env_3764_ = lean_ctor_get(v___x_3763_, 0);
                lean_inc_ref(v_env_3764_);
                lean_dec(v___x_3763_);
                v___x_3765_ = 0;
                lean_inc(v_constName_3757_);
                v___x_3766_ =
                    l_Lean_Environment_find_x3f(v_env_3764_, v_constName_3757_, v___x_3765_);
                if lean_obj_tag(v___x_3766_) == 0 {
                    v___x_3767_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
                    return v___x_3767_;
                } else {
                    lean_dec(v_constName_3757_);
                    v_val_3768_ = lean_ctor_get(v___x_3766_, 0);
                    v_isSharedCheck_3775_ = (!lean_is_exclusive(v___x_3766_)) as u8;
                    if v_isSharedCheck_3775_ == 0 {
                        v___x_3770_ = v___x_3766_;
                        v_isShared_3771_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3768_);
                        lean_dec(v___x_3766_);
                        v___x_3770_ = lean_box(0);
                        v_isShared_3771_ = v_isSharedCheck_3775_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3771_ == 0 {
                    lean_ctor_set_tag(v___x_3770_, 0);
                    v___x_3773_ = v___x_3770_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_val_3768_);
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
    mut v_constName_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3782_: *mut LeanObject = core::ptr::null_mut();
    v_res_3782_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
    lean_dec(v___y_3780_);
    lean_dec_ref(v___y_3779_);
    lean_dec(v___y_3778_);
    lean_dec_ref(v___y_3777_);
    return v_res_3782_;
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(
    mut v_msg_3783_: *mut LeanObject,
    mut v___y_3784_: *mut LeanObject,
    mut v___y_3785_: *mut LeanObject,
    mut v___y_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3809_: u8 = 0;
    let mut v_toFunctor_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3816_: u8 = 0;
    let mut v___f_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921__overap_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v_unused_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_unused_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3789_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1,
                );
                v_toApplicative_3790_ = lean_ctor_get(v___x_3789_, 0);
                v_toFunctor_3791_ = lean_ctor_get(v_toApplicative_3790_, 0);
                v_toSeq_3792_ = lean_ctor_get(v_toApplicative_3790_, 2);
                v_toSeqLeft_3793_ = lean_ctor_get(v_toApplicative_3790_, 3);
                v_toSeqRight_3794_ = lean_ctor_get(v_toApplicative_3790_, 4);
                v___f_3795_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2;
                v___f_3796_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3;
                lean_inc_ref_n(v_toFunctor_3791_, 2);
                v___f_3797_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3797_, 0, v_toFunctor_3791_);
                v___f_3798_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3798_, 0, v_toFunctor_3791_);
                v___x_3799_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3799_, 0, v___f_3797_);
                lean_ctor_set(v___x_3799_, 1, v___f_3798_);
                lean_inc(v_toSeqRight_3794_);
                v___f_3800_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3800_, 0, v_toSeqRight_3794_);
                lean_inc(v_toSeqLeft_3793_);
                v___f_3801_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3801_, 0, v_toSeqLeft_3793_);
                lean_inc(v_toSeq_3792_);
                v___f_3802_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3802_, 0, v_toSeq_3792_);
                v___x_3803_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3803_, 0, v___x_3799_);
                lean_ctor_set(v___x_3803_, 1, v___f_3795_);
                lean_ctor_set(v___x_3803_, 2, v___f_3802_);
                lean_ctor_set(v___x_3803_, 3, v___f_3801_);
                lean_ctor_set(v___x_3803_, 4, v___f_3800_);
                v___x_3804_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3804_, 0, v___x_3803_);
                lean_ctor_set(v___x_3804_, 1, v___f_3796_);
                v___x_3805_ = l_StateRefT_x27_instMonad___redArg(v___x_3804_);
                v_toApplicative_3806_ = lean_ctor_get(v___x_3805_, 0);
                v_isSharedCheck_3837_ = (!lean_is_exclusive(v___x_3805_)) as u8;
                if v_isSharedCheck_3837_ == 0 {
                    v_unused_3838_ = lean_ctor_get(v___x_3805_, 1);
                    lean_dec(v_unused_3838_);
                    v___x_3808_ = v___x_3805_;
                    v_isShared_3809_ = v_isSharedCheck_3837_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3806_);
                    lean_dec(v___x_3805_);
                    v___x_3808_ = lean_box(0);
                    v_isShared_3809_ = v_isSharedCheck_3837_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3810_ = lean_ctor_get(v_toApplicative_3806_, 0);
                v_toSeq_3811_ = lean_ctor_get(v_toApplicative_3806_, 2);
                v_toSeqLeft_3812_ = lean_ctor_get(v_toApplicative_3806_, 3);
                v_toSeqRight_3813_ = lean_ctor_get(v_toApplicative_3806_, 4);
                v_isSharedCheck_3835_ = (!lean_is_exclusive(v_toApplicative_3806_)) as u8;
                if v_isSharedCheck_3835_ == 0 {
                    v_unused_3836_ = lean_ctor_get(v_toApplicative_3806_, 1);
                    lean_dec(v_unused_3836_);
                    v___x_3815_ = v_toApplicative_3806_;
                    v_isShared_3816_ = v_isSharedCheck_3835_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3813_);
                    lean_inc(v_toSeqLeft_3812_);
                    lean_inc(v_toSeq_3811_);
                    lean_inc(v_toFunctor_3810_);
                    lean_dec(v_toApplicative_3806_);
                    v___x_3815_ = lean_box(0);
                    v_isShared_3816_ = v_isSharedCheck_3835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3817_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4;
                v___f_3818_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5;
                lean_inc_ref(v_toFunctor_3810_);
                v___f_3819_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3819_, 0, v_toFunctor_3810_);
                v___f_3820_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3820_, 0, v_toFunctor_3810_);
                v___x_3821_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3821_, 0, v___f_3819_);
                lean_ctor_set(v___x_3821_, 1, v___f_3820_);
                v___f_3822_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3822_, 0, v_toSeqRight_3813_);
                v___f_3823_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3823_, 0, v_toSeqLeft_3812_);
                v___f_3824_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3824_, 0, v_toSeq_3811_);
                if v_isShared_3816_ == 0 {
                    lean_ctor_set(v___x_3815_, 4, v___f_3822_);
                    lean_ctor_set(v___x_3815_, 3, v___f_3823_);
                    lean_ctor_set(v___x_3815_, 2, v___f_3824_);
                    lean_ctor_set(v___x_3815_, 1, v___f_3817_);
                    lean_ctor_set(v___x_3815_, 0, v___x_3821_);
                    v___x_3826_ = v___x_3815_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3821_);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___f_3817_);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 2, v___f_3824_);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 3, v___f_3823_);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 4, v___f_3822_);
                    v___x_3826_ = v_reuseFailAlloc_3834_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3809_ == 0 {
                    lean_ctor_set(v___x_3808_, 1, v___f_3818_);
                    lean_ctor_set(v___x_3808_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3808_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3826_);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 1, v___f_3818_);
                    v___x_3828_ = v_reuseFailAlloc_3833_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3829_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
                v___x_3830_ = l_instInhabitedOfMonad___redArg(v___x_3828_, v___x_3829_);
                v___x_2921__overap_3831_ = lean_panic_fn_borrowed(v___x_3830_, v_msg_3783_);
                lean_dec(v___x_3830_);
                lean_inc(v___y_3787_);
                lean_inc_ref(v___y_3786_);
                lean_inc(v___y_3785_);
                lean_inc_ref(v___y_3784_);
                v___x_3832_ = lean_apply_5(
                    v___x_2921__overap_3831_,
                    v___y_3784_,
                    v___y_3785_,
                    v___y_3786_,
                    v___y_3787_,
                    lean_box(0),
                );
                return v___x_3832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(
    mut v_msg_3839_: *mut LeanObject,
    mut v___y_3840_: *mut LeanObject,
    mut v___y_3841_: *mut LeanObject,
    mut v___y_3842_: *mut LeanObject,
    mut v___y_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3845_: *mut LeanObject = core::ptr::null_mut();
    v_res_3845_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
    lean_dec(v___y_3843_);
    lean_dec_ref(v___y_3842_);
    lean_dec(v___y_3841_);
    lean_dec_ref(v___y_3840_);
    return v_res_3845_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2;
    v___x_3850_ = lean_unsigned_to_nat(53);
    v___x_3851_ = lean_unsigned_to_nat(62);
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
    mut v_bs_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
    mut v___y_3861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: usize = 0;
    let mut v___x_3873_: usize = 0;
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: u8 = 0;
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v_a_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3863_ = lean_usize_dec_lt(v_i_3856_, v_sz_3855_);
                if v___x_3863_ == 0 {
                    v___x_3864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3864_, 0, v_bs_3857_);
                    return v___x_3864_;
                } else {
                    v_v_3865_ = lean_array_uget_borrowed(v_bs_3857_, v_i_3856_);
                    lean_inc(v_v_3865_);
                    v___x_3866_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_3865_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
                    if lean_obj_tag(v___x_3866_) == 0 {
                        v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
                        lean_inc(v_a_3867_);
                        lean_dec_ref_known(v___x_3866_, 1);
                        v___x_3868_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3869_ = lean_array_uset(v_bs_3857_, v_i_3856_, v___x_3868_);
                        if lean_obj_tag(v_a_3867_) == 6 {
                            v_val_3876_ = lean_ctor_get(v_a_3867_, 0);
                            lean_inc_ref(v_val_3876_);
                            lean_dec_ref_known(v_a_3867_, 1);
                            v_numFields_3877_ = lean_ctor_get(v_val_3876_, 4);
                            lean_inc(v_numFields_3877_);
                            lean_dec_ref(v_val_3876_);
                            v___x_3878_ = 0;
                            v___x_3879_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v___x_3879_, 0, v_numFields_3877_);
                            lean_ctor_set(v___x_3879_, 1, v___x_3868_);
                            lean_ctor_set_uint8(
                                v___x_3879_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v___x_3878_,
                            );
                            v_a_3871_ = v___x_3879_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3867_);
                            v___x_3880_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
                            v___x_3881_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_3880_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
                            if lean_obj_tag(v___x_3881_) == 0 {
                                v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
                                lean_inc(v_a_3882_);
                                lean_dec_ref_known(v___x_3881_, 1);
                                v_a_3871_ = v_a_3882_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_bs_x27_3869_);
                                v_a_3883_ = lean_ctor_get(v___x_3881_, 0);
                                v_isSharedCheck_3890_ = (!lean_is_exclusive(v___x_3881_)) as u8;
                                if v_isSharedCheck_3890_ == 0 {
                                    v___x_3885_ = v___x_3881_;
                                    v_isShared_3886_ = v_isSharedCheck_3890_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3883_);
                                    lean_dec(v___x_3881_);
                                    v___x_3885_ = lean_box(0);
                                    v_isShared_3886_ = v_isSharedCheck_3890_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_bs_3857_);
                        v_a_3891_ = lean_ctor_get(v___x_3866_, 0);
                        v_isSharedCheck_3898_ = (!lean_is_exclusive(v___x_3866_)) as u8;
                        if v_isSharedCheck_3898_ == 0 {
                            v___x_3893_ = v___x_3866_;
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3891_);
                            lean_dec(v___x_3866_);
                            v___x_3893_ = lean_box(0);
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
                    v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
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
                    v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
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
    mut v_sz_3899_: *mut LeanObject,
    mut v_i_3900_: *mut LeanObject,
    mut v_bs_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3907_: usize = 0;
    let mut v_i_boxed_3908_: usize = 0;
    let mut v_res_3909_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3907_ = lean_unbox_usize(v_sz_3899_);
    lean_dec(v_sz_3899_);
    v_i_boxed_3908_ = lean_unbox_usize(v_i_3900_);
    lean_dec(v_i_3900_);
    v_res_3909_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_3907_, v_i_boxed_3908_, v_bs_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
    lean_dec(v___y_3905_);
    lean_dec_ref(v___y_3904_);
    lean_dec(v___y_3903_);
    lean_dec_ref(v___y_3902_);
    return v_res_3909_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3911_: *mut LeanObject = core::ptr::null_mut();
    v___x_3910_ = lean_box(0);
    v_dummy_3911_ = l_Lean_Expr_sort___override(v___x_3910_);
    return v_dummy_3911_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    v___x_3912_ = lean_box(0);
    v___x_3913_ = lean_unsigned_to_nat(16);
    v___x_3914_ = lean_mk_array(v___x_3913_, v___x_3912_);
    return v___x_3914_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    v___x_3915_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
    v___x_3916_ = lean_unsigned_to_nat(0);
    v___x_3917_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3917_, 0, v___x_3916_);
    lean_ctor_set(v___x_3917_, 1, v___x_3915_);
    return v___x_3917_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(
    mut v_e_3920_: *mut LeanObject,
    mut v_alsoCasesOn_3921_: u8,
    mut v___y_3922_: *mut LeanObject,
    mut v___y_3923_: *mut LeanObject,
    mut v___y_3924_: *mut LeanObject,
    mut v___y_3925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: u8 = 0;
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v_val_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v_dummy_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v_numParams_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3983_: u8 = 0;
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v_indName_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3992_: u8 = 0;
    let mut v_val_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3996_: u8 = 0;
    let mut v_toConstantVal_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4031_: usize = 0;
    let mut v___x_4032_: usize = 0;
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4037_: u8 = 0;
    let mut v_start_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v_a_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_lower_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u8 = 0;
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_a_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut v_isSharedCheck_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3930_ = l_Lean_Expr_isApp(v_e_3920_);
                if v___x_3930_ == 0 {
                    lean_dec_ref(v_e_3920_);
                    v___x_3931_ = lean_box(0);
                    v___x_3932_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3932_, 0, v___x_3931_);
                    return v___x_3932_;
                } else {
                    v___x_3933_ = l_Lean_Expr_getAppFn(v_e_3920_);
                    if lean_obj_tag(v___x_3933_) == 4 {
                        v_declName_3934_ = lean_ctor_get(v___x_3933_, 0);
                        lean_inc_n(v_declName_3934_, 2);
                        v_us_3935_ = lean_ctor_get(v___x_3933_, 1);
                        lean_inc(v_us_3935_);
                        lean_dec_ref_known(v___x_3933_, 2);
                        v___x_3936_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_3934_, v___y_3925_);
                        v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
                        v_isSharedCheck_4091_ = (!lean_is_exclusive(v___x_3936_)) as u8;
                        if v_isSharedCheck_4091_ == 0 {
                            v___x_3939_ = v___x_3936_;
                            v_isShared_3940_ = v_isSharedCheck_4091_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3937_);
                            lean_dec(v___x_3936_);
                            v___x_3939_ = lean_box(0);
                            v_isShared_3940_ = v_isSharedCheck_4091_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3933_);
                        lean_dec_ref(v_e_3920_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3928_ = lean_box(0);
                v___x_3929_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                return v___x_3929_;
            }
            2 => {
                if lean_obj_tag(v_a_3937_) == 1 {
                    v_val_3941_ = lean_ctor_get(v_a_3937_, 0);
                    v_isSharedCheck_3983_ = (!lean_is_exclusive(v_a_3937_)) as u8;
                    if v_isSharedCheck_3983_ == 0 {
                        v___x_3943_ = v_a_3937_;
                        v_isShared_3944_ = v_isSharedCheck_3983_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_3941_);
                        lean_dec(v_a_3937_);
                        v___x_3943_ = lean_box(0);
                        v_isShared_3944_ = v_isSharedCheck_3983_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3939_);
                    lean_dec(v_a_3937_);
                    v___x_3984_ = lean_st_ref_get(v___y_3925_);
                    if v_alsoCasesOn_3921_ == 0 {
                        lean_dec(v___x_3984_);
                        lean_dec(v_us_3935_);
                        lean_dec(v_declName_3934_);
                        lean_dec_ref(v_e_3920_);
                        state = 1;
                        continue;
                    } else {
                        v_env_3985_ = lean_ctor_get(v___x_3984_, 0);
                        lean_inc_ref(v_env_3985_);
                        lean_dec(v___x_3984_);
                        lean_inc(v_declName_3934_);
                        v___x_3986_ = l_Lean_isCasesOnRecursor(v_env_3985_, v_declName_3934_);
                        if v___x_3986_ == 0 {
                            lean_dec(v_us_3935_);
                            lean_dec(v_declName_3934_);
                            lean_dec_ref(v_e_3920_);
                            state = 1;
                            continue;
                        } else {
                            v_indName_3987_ = l_Lean_Name_getPrefix(v_declName_3934_);
                            v___x_3988_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_3987_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
                            if lean_obj_tag(v___x_3988_) == 0 {
                                v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
                                v_isSharedCheck_4082_ = (!lean_is_exclusive(v___x_3988_)) as u8;
                                if v_isSharedCheck_4082_ == 0 {
                                    v___x_3991_ = v___x_3988_;
                                    v_isShared_3992_ = v_isSharedCheck_4082_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3989_);
                                    lean_dec(v___x_3988_);
                                    v___x_3991_ = lean_box(0);
                                    v_isShared_3992_ = v_isSharedCheck_4082_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v_us_3935_);
                                lean_dec(v_declName_3934_);
                                lean_dec_ref(v_e_3920_);
                                v_a_4083_ = lean_ctor_get(v___x_3988_, 0);
                                v_isSharedCheck_4090_ = (!lean_is_exclusive(v___x_3988_)) as u8;
                                if v_isSharedCheck_4090_ == 0 {
                                    v___x_4085_ = v___x_3988_;
                                    v_isShared_4086_ = v_isSharedCheck_4090_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_4083_);
                                    lean_dec(v___x_3988_);
                                    v___x_4085_ = lean_box(0);
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
                v_dummy_3945_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
                v_nargs_3946_ = l_Lean_Expr_getAppNumArgs(v_e_3920_);
                lean_inc(v_nargs_3946_);
                v___x_3947_ = lean_mk_array(v_nargs_3946_, v_dummy_3945_);
                v___x_3948_ = lean_unsigned_to_nat(1);
                v___x_3949_ = lean_nat_sub(v_nargs_3946_, v___x_3948_);
                lean_dec(v_nargs_3946_);
                v_args_3950_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_3920_,
                    v___x_3947_,
                    v___x_3949_,
                );
                v___x_3951_ = lean_array_get_size(v_args_3950_);
                v___x_3952_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_3941_);
                v___x_3953_ = lean_nat_dec_lt(v___x_3951_, v___x_3952_);
                lean_dec(v___x_3952_);
                if v___x_3953_ == 0 {
                    v_numParams_3954_ = lean_ctor_get(v_val_3941_, 0);
                    v_numDiscrs_3955_ = lean_ctor_get(v_val_3941_, 1);
                    v___x_3956_ = lean_array_mk(v_us_3935_);
                    v___x_3957_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_3954_);
                    v___x_3958_ =
                        l_Array_extract___redArg(v_args_3950_, v___x_3957_, v_numParams_3954_);
                    v___x_3959_ = l_Lean_instInhabitedExpr;
                    v___x_3960_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_3941_);
                    v___x_3961_ = lean_array_get(v___x_3959_, v_args_3950_, v___x_3960_);
                    lean_dec(v___x_3960_);
                    v___x_3962_ = lean_nat_add(v_numParams_3954_, v___x_3948_);
                    v___x_3963_ = lean_nat_add(v___x_3962_, v_numDiscrs_3955_);
                    lean_inc(v___x_3963_);
                    lean_inc_ref_n(v_args_3950_, 2);
                    v___x_3964_ =
                        l_Array_toSubarray___redArg(v_args_3950_, v___x_3962_, v___x_3963_);
                    v___x_3965_ = l_Subarray_copy___redArg(v___x_3964_);
                    v___x_3966_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_3941_);
                    v___x_3967_ = lean_nat_add(v___x_3963_, v___x_3966_);
                    lean_dec(v___x_3966_);
                    lean_inc(v___x_3967_);
                    v___x_3968_ =
                        l_Array_toSubarray___redArg(v_args_3950_, v___x_3963_, v___x_3967_);
                    v___x_3969_ = l_Subarray_copy___redArg(v___x_3968_);
                    v___x_3970_ =
                        l_Array_toSubarray___redArg(v_args_3950_, v___x_3967_, v___x_3951_);
                    v___x_3971_ = l_Subarray_copy___redArg(v___x_3970_);
                    v___x_3972_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_3972_, 0, v_val_3941_);
                    lean_ctor_set(v___x_3972_, 1, v_declName_3934_);
                    lean_ctor_set(v___x_3972_, 2, v___x_3956_);
                    lean_ctor_set(v___x_3972_, 3, v___x_3958_);
                    lean_ctor_set(v___x_3972_, 4, v___x_3961_);
                    lean_ctor_set(v___x_3972_, 5, v___x_3965_);
                    lean_ctor_set(v___x_3972_, 6, v___x_3969_);
                    lean_ctor_set(v___x_3972_, 7, v___x_3971_);
                    if v_isShared_3944_ == 0 {
                        lean_ctor_set(v___x_3943_, 0, v___x_3972_);
                        v___x_3974_ = v___x_3943_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3972_);
                        v___x_3974_ = v_reuseFailAlloc_3978_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_3950_);
                    lean_del_object(v___x_3943_);
                    lean_dec(v_val_3941_);
                    lean_dec(v_us_3935_);
                    lean_dec(v_declName_3934_);
                    v___x_3979_ = lean_box(0);
                    if v_isShared_3940_ == 0 {
                        lean_ctor_set(v___x_3939_, 0, v___x_3979_);
                        v___x_3981_ = v___x_3939_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3979_);
                        v___x_3981_ = v_reuseFailAlloc_3982_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3940_ == 0 {
                    lean_ctor_set(v___x_3939_, 0, v___x_3974_);
                    v___x_3976_ = v___x_3939_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
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
                if lean_obj_tag(v_a_3989_) == 5 {
                    v_val_3993_ = lean_ctor_get(v_a_3989_, 0);
                    v_isSharedCheck_4077_ = (!lean_is_exclusive(v_a_3989_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_3995_ = v_a_3989_;
                        v_isShared_3996_ = v_isSharedCheck_4077_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_3993_);
                        lean_dec(v_a_3989_);
                        v___x_3995_ = lean_box(0);
                        v_isShared_3996_ = v_isSharedCheck_4077_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3989_);
                    lean_dec(v_us_3935_);
                    lean_dec(v_declName_3934_);
                    lean_dec_ref(v_e_3920_);
                    v___x_4078_ = lean_box(0);
                    if v_isShared_3992_ == 0 {
                        lean_ctor_set(v___x_3991_, 0, v___x_4078_);
                        v___x_4080_ = v___x_3991_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4078_);
                        v___x_4080_ = v_reuseFailAlloc_4081_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                v_toConstantVal_3997_ = lean_ctor_get(v_val_3993_, 0);
                lean_inc_ref(v_toConstantVal_3997_);
                v_numParams_3998_ = lean_ctor_get(v_val_3993_, 1);
                lean_inc(v_numParams_3998_);
                v_numIndices_3999_ = lean_ctor_get(v_val_3993_, 2);
                lean_inc(v_numIndices_3999_);
                v_ctors_4000_ = lean_ctor_get(v_val_3993_, 4);
                lean_inc(v_ctors_4000_);
                v_nargs_4001_ = l_Lean_Expr_getAppNumArgs(v_e_3920_);
                v_dummy_4002_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
                lean_inc(v_nargs_4001_);
                v___x_4003_ = lean_mk_array(v_nargs_4001_, v_dummy_4002_);
                v___x_4004_ = lean_unsigned_to_nat(1);
                v___x_4005_ = lean_nat_sub(v_nargs_4001_, v___x_4004_);
                lean_dec(v_nargs_4001_);
                v_args_4006_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_3920_,
                    v___x_4003_,
                    v___x_4005_,
                );
                v___x_4007_ = lean_nat_add(v_numParams_3998_, v___x_4004_);
                v___x_4008_ = lean_nat_add(v___x_4007_, v_numIndices_3999_);
                v___x_4009_ = lean_nat_add(v___x_4008_, v___x_4004_);
                lean_dec(v___x_4008_);
                v___x_4010_ = l_Lean_InductiveVal_numCtors(v_val_3993_);
                lean_dec_ref(v_val_3993_);
                v___x_4011_ = lean_nat_add(v___x_4009_, v___x_4010_);
                lean_dec(v___x_4010_);
                v___x_4012_ = lean_array_get_size(v_args_4006_);
                v___x_4013_ = lean_nat_dec_le(v___x_4011_, v___x_4012_);
                if v___x_4013_ == 0 {
                    lean_dec(v___x_4011_);
                    lean_dec(v___x_4009_);
                    lean_dec(v___x_4007_);
                    lean_dec_ref(v_args_4006_);
                    lean_dec(v_ctors_4000_);
                    lean_dec(v_numIndices_3999_);
                    lean_dec(v_numParams_3998_);
                    lean_dec_ref(v_toConstantVal_3997_);
                    lean_del_object(v___x_3995_);
                    lean_dec(v_us_3935_);
                    lean_dec(v_declName_3934_);
                    v___x_4014_ = lean_box(0);
                    if v_isShared_3992_ == 0 {
                        lean_ctor_set(v___x_3991_, 0, v___x_4014_);
                        v___x_4016_ = v___x_3991_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4014_);
                        v___x_4016_ = v_reuseFailAlloc_4017_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3991_);
                    v___x_4018_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_3998_);
                    lean_inc_ref_n(v_args_4006_, 3);
                    v_params_4019_ =
                        l_Array_toSubarray___redArg(v_args_4006_, v___x_4018_, v_numParams_3998_);
                    v___x_4020_ = l_Lean_instInhabitedExpr;
                    v_motive_4021_ = lean_array_get(v___x_4020_, v_args_4006_, v_numParams_3998_);
                    lean_dec(v_numParams_3998_);
                    lean_inc(v___x_4009_);
                    v_discrs_4022_ =
                        l_Array_toSubarray___redArg(v_args_4006_, v___x_4007_, v___x_4009_);
                    v___x_4023_ = lean_nat_add(v_numIndices_3999_, v___x_4004_);
                    lean_dec(v_numIndices_3999_);
                    v___x_4024_ = lean_box(0);
                    v_discrInfos_4025_ = lean_mk_array(v___x_4023_, v___x_4024_);
                    lean_inc(v___x_4011_);
                    v_alts_4026_ =
                        l_Array_toSubarray___redArg(v_args_4006_, v___x_4009_, v___x_4011_);
                    v___x_4076_ = lean_nat_dec_le(v___x_4011_, v___x_4018_);
                    if v___x_4076_ == 0 {
                        v_lower_4068_ = v___x_4011_;
                        v_upper_4069_ = v___x_4012_;
                        state = 16;
                        continue;
                    } else {
                        lean_dec(v___x_4011_);
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
                if lean_obj_tag(v___x_4033_) == 0 {
                    v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
                    v_isSharedCheck_4058_ = (!lean_is_exclusive(v___x_4033_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4036_ = v___x_4033_;
                        v_isShared_4037_ = v_isSharedCheck_4058_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4034_);
                        lean_dec(v___x_4033_);
                        v___x_4036_ = lean_box(0);
                        v_isShared_4037_ = v_isSharedCheck_4058_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v___y_4029_);
                    lean_dec_ref(v___y_4028_);
                    lean_dec_ref(v_alts_4026_);
                    lean_dec_ref(v_discrInfos_4025_);
                    lean_dec_ref(v_discrs_4022_);
                    lean_dec(v_motive_4021_);
                    lean_dec_ref(v_params_4019_);
                    lean_del_object(v___x_3995_);
                    lean_dec(v_us_3935_);
                    lean_dec(v_declName_3934_);
                    v_a_4059_ = lean_ctor_get(v___x_4033_, 0);
                    v_isSharedCheck_4066_ = (!lean_is_exclusive(v___x_4033_)) as u8;
                    if v_isSharedCheck_4066_ == 0 {
                        v___x_4061_ = v___x_4033_;
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_4059_);
                        lean_dec(v___x_4033_);
                        v___x_4061_ = lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_start_4038_ = lean_ctor_get(v_params_4019_, 1);
                lean_inc(v_start_4038_);
                v_stop_4039_ = lean_ctor_get(v_params_4019_, 2);
                lean_inc(v_stop_4039_);
                v_start_4040_ = lean_ctor_get(v_discrs_4022_, 1);
                lean_inc(v_start_4040_);
                v_stop_4041_ = lean_ctor_get(v_discrs_4022_, 2);
                lean_inc(v_stop_4041_);
                v___x_4042_ = lean_nat_sub(v_stop_4039_, v_start_4038_);
                lean_dec(v_start_4038_);
                lean_dec(v_stop_4039_);
                v___x_4043_ = lean_nat_sub(v_stop_4041_, v_start_4040_);
                lean_dec(v_start_4040_);
                lean_dec(v_stop_4041_);
                v___x_4044_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
                v___x_4045_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_4045_, 0, v___x_4042_);
                lean_ctor_set(v___x_4045_, 1, v___x_4043_);
                lean_ctor_set(v___x_4045_, 2, v_a_4034_);
                lean_ctor_set(v___x_4045_, 3, v___y_4029_);
                lean_ctor_set(v___x_4045_, 4, v_discrInfos_4025_);
                lean_ctor_set(v___x_4045_, 5, v___x_4044_);
                v___x_4046_ = lean_array_mk(v_us_3935_);
                v___x_4047_ = l_Subarray_copy___redArg(v_params_4019_);
                v___x_4048_ = l_Subarray_copy___redArg(v_discrs_4022_);
                v___x_4049_ = l_Subarray_copy___redArg(v_alts_4026_);
                v___x_4050_ = l_Subarray_copy___redArg(v___y_4028_);
                v___x_4051_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_4051_, 0, v___x_4045_);
                lean_ctor_set(v___x_4051_, 1, v_declName_3934_);
                lean_ctor_set(v___x_4051_, 2, v___x_4046_);
                lean_ctor_set(v___x_4051_, 3, v___x_4047_);
                lean_ctor_set(v___x_4051_, 4, v_motive_4021_);
                lean_ctor_set(v___x_4051_, 5, v___x_4048_);
                lean_ctor_set(v___x_4051_, 6, v___x_4049_);
                lean_ctor_set(v___x_4051_, 7, v___x_4050_);
                if v_isShared_3996_ == 0 {
                    lean_ctor_set_tag(v___x_3995_, 1);
                    lean_ctor_set(v___x_3995_, 0, v___x_4051_);
                    v___x_4053_ = v___x_3995_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4051_);
                    v___x_4053_ = v_reuseFailAlloc_4057_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4037_ == 0 {
                    lean_ctor_set(v___x_4036_, 0, v___x_4053_);
                    v___x_4055_ = v___x_4036_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
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
                    v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4064_;
            }
            16 => {
                v_levelParams_4070_ = lean_ctor_get(v_toConstantVal_3997_, 1);
                lean_inc(v_levelParams_4070_);
                lean_dec_ref(v_toConstantVal_3997_);
                v___x_4071_ =
                    l_Array_toSubarray___redArg(v_args_4006_, v_lower_4068_, v_upper_4069_);
                v___x_4072_ = l_List_lengthTR___redArg(v_levelParams_4070_);
                lean_dec(v_levelParams_4070_);
                v___x_4073_ = l_List_lengthTR___redArg(v_us_3935_);
                v___x_4074_ = lean_nat_dec_eq(v___x_4072_, v___x_4073_);
                lean_dec(v___x_4073_);
                lean_dec(v___x_4072_);
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
                    v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
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
    mut v_e_4092_: *mut LeanObject,
    mut v_alsoCasesOn_4093_: *mut LeanObject,
    mut v___y_4094_: *mut LeanObject,
    mut v___y_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_alsoCasesOn_boxed_4099_: u8 = 0;
    let mut v_res_4100_: *mut LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_4099_ = (lean_unbox(v_alsoCasesOn_4093_) as u8);
    v_res_4100_ =
        l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(
            v_e_4092_,
            v_alsoCasesOn_boxed_4099_,
            v___y_4094_,
            v___y_4095_,
            v___y_4096_,
            v___y_4097_,
        );
    lean_dec(v___y_4097_);
    lean_dec_ref(v___y_4096_);
    lean_dec(v___y_4095_);
    lean_dec_ref(v___y_4094_);
    return v_res_4100_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(
    mut v_e_4101_: *mut LeanObject,
    mut v_a_4102_: *mut LeanObject,
    mut v_a_4103_: *mut LeanObject,
    mut v_a_4104_: *mut LeanObject,
    mut v_a_4105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: u8 = 0;
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v_val_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4133_: u8 = 0;
    let mut v_a_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
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
                        if lean_obj_tag(v___x_4112_) == 0 {
                            v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
                            v_isSharedCheck_4133_ = (!lean_is_exclusive(v___x_4112_)) as u8;
                            if v_isSharedCheck_4133_ == 0 {
                                v___x_4115_ = v___x_4112_;
                                v_isShared_4116_ = v_isSharedCheck_4133_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4113_);
                                lean_dec(v___x_4112_);
                                v___x_4115_ = lean_box(0);
                                v_isShared_4116_ = v_isSharedCheck_4133_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4134_ = lean_ctor_get(v___x_4112_, 0);
                            v_isSharedCheck_4141_ = (!lean_is_exclusive(v___x_4112_)) as u8;
                            if v_isSharedCheck_4141_ == 0 {
                                v___x_4136_ = v___x_4112_;
                                v_isShared_4137_ = v_isSharedCheck_4141_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_4134_);
                                lean_dec(v___x_4112_);
                                v___x_4136_ = lean_box(0);
                                v_isShared_4137_ = v_isSharedCheck_4141_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        v___x_4142_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4142_, 0, v_e_4101_);
                        v___x_4143_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4143_, 0, v___x_4142_);
                        v___x_4144_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4144_, 0, v___x_4143_);
                        return v___x_4144_;
                    }
                } else {
                    v___x_4145_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4145_, 0, v_e_4101_);
                    v___x_4146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4146_, 0, v___x_4145_);
                    v___x_4147_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4147_, 0, v___x_4146_);
                    return v___x_4147_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_4113_) == 1 {
                    v_val_4117_ = lean_ctor_get(v_a_4113_, 0);
                    v_isSharedCheck_4128_ = (!lean_is_exclusive(v_a_4113_)) as u8;
                    if v_isSharedCheck_4128_ == 0 {
                        v___x_4119_ = v_a_4113_;
                        v_isShared_4120_ = v_isSharedCheck_4128_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4117_);
                        lean_dec(v_a_4113_);
                        v___x_4119_ = lean_box(0);
                        v_isShared_4120_ = v_isSharedCheck_4128_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4113_);
                    v___x_4129_ = lean_box(0);
                    if v_isShared_4116_ == 0 {
                        lean_ctor_set(v___x_4115_, 0, v___x_4129_);
                        v___x_4131_ = v___x_4115_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
                        v___x_4131_ = v_reuseFailAlloc_4132_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4121_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_4121_, 0, v_val_4117_);
                if v_isShared_4120_ == 0 {
                    lean_ctor_set(v___x_4119_, 0, v___x_4121_);
                    v___x_4123_ = v___x_4119_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4121_);
                    v___x_4123_ = v_reuseFailAlloc_4127_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4116_ == 0 {
                    lean_ctor_set(v___x_4115_, 0, v___x_4123_);
                    v___x_4125_ = v___x_4115_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4123_);
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
                    v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
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
    mut v_e_4148_: *mut LeanObject,
    mut v_a_4149_: *mut LeanObject,
    mut v_a_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
    mut v_a_4152_: *mut LeanObject,
    mut v_a_4153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4154_: *mut LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(
        v_e_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_,
    );
    lean_dec(v_a_4152_);
    lean_dec_ref(v_a_4151_);
    lean_dec(v_a_4150_);
    lean_dec_ref(v_a_4149_);
    return v_res_4154_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(
    mut v_declName_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
    mut v___y_4157_: *mut LeanObject,
    mut v___y_4158_: *mut LeanObject,
    mut v___y_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    v___x_4161_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_4155_, v___y_4159_);
    return v___x_4161_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(
    mut v_declName_4162_: *mut LeanObject,
    mut v___y_4163_: *mut LeanObject,
    mut v___y_4164_: *mut LeanObject,
    mut v___y_4165_: *mut LeanObject,
    mut v___y_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4168_: *mut LeanObject = core::ptr::null_mut();
    v_res_4168_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
    lean_dec(v___y_4166_);
    lean_dec_ref(v___y_4165_);
    lean_dec(v___y_4164_);
    lean_dec_ref(v___y_4163_);
    return v_res_4168_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4169_: *mut LeanObject,
    mut v_constName_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
    mut v___y_4173_: *mut LeanObject,
    mut v___y_4174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    v___x_4176_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
    return v___x_4176_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4177_: *mut LeanObject,
    mut v_constName_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4184_: *mut LeanObject = core::ptr::null_mut();
    v_res_4184_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_4177_, v_constName_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
    lean_dec(v___y_4182_);
    lean_dec_ref(v___y_4181_);
    lean_dec(v___y_4180_);
    lean_dec_ref(v___y_4179_);
    return v_res_4184_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_4185_: *mut LeanObject,
    mut v_ref_4186_: *mut LeanObject,
    mut v_constName_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    v___x_4193_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_4186_, v_constName_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
    return v___x_4193_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_4194_: *mut LeanObject,
    mut v_ref_4195_: *mut LeanObject,
    mut v_constName_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4202_: *mut LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_4194_, v_ref_4195_, v_constName_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
    lean_dec(v___y_4200_);
    lean_dec_ref(v___y_4199_);
    lean_dec(v___y_4198_);
    lean_dec_ref(v___y_4197_);
    lean_dec(v_ref_4195_);
    return v_res_4202_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_4203_: *mut LeanObject,
    mut v_ref_4204_: *mut LeanObject,
    mut v_msg_4205_: *mut LeanObject,
    mut v_declHint_4206_: *mut LeanObject,
    mut v___y_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    v___x_4212_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_4204_, v_msg_4205_, v_declHint_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
    return v___x_4212_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_4213_: *mut LeanObject,
    mut v_ref_4214_: *mut LeanObject,
    mut v_msg_4215_: *mut LeanObject,
    mut v_declHint_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4222_: *mut LeanObject = core::ptr::null_mut();
    v_res_4222_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_4213_, v_ref_4214_, v_msg_4215_, v_declHint_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
    lean_dec(v___y_4220_);
    lean_dec_ref(v___y_4219_);
    lean_dec(v___y_4218_);
    lean_dec_ref(v___y_4217_);
    lean_dec(v_ref_4214_);
    return v_res_4222_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(
    mut v_msg_4223_: *mut LeanObject,
    mut v_declHint_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
    mut v___y_4227_: *mut LeanObject,
    mut v___y_4228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_4223_, v_declHint_4224_, v___y_4228_);
    return v___x_4230_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(
    mut v_msg_4231_: *mut LeanObject,
    mut v_declHint_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
    mut v___y_4235_: *mut LeanObject,
    mut v___y_4236_: *mut LeanObject,
    mut v___y_4237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4238_: *mut LeanObject = core::ptr::null_mut();
    v_res_4238_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_4231_, v_declHint_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
    lean_dec(v___y_4236_);
    lean_dec_ref(v___y_4235_);
    lean_dec(v___y_4234_);
    lean_dec_ref(v___y_4233_);
    return v_res_4238_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(
    mut v_00_u03b1_4239_: *mut LeanObject,
    mut v_ref_4240_: *mut LeanObject,
    mut v_msg_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
    mut v___y_4243_: *mut LeanObject,
    mut v___y_4244_: *mut LeanObject,
    mut v___y_4245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_4240_, v_msg_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
    return v___x_4247_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_4248_: *mut LeanObject,
    mut v_ref_4249_: *mut LeanObject,
    mut v_msg_4250_: *mut LeanObject,
    mut v___y_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4256_: *mut LeanObject = core::ptr::null_mut();
    v_res_4256_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_4248_, v_ref_4249_, v_msg_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
    lean_dec(v___y_4254_);
    lean_dec_ref(v___y_4253_);
    lean_dec(v___y_4252_);
    lean_dec_ref(v___y_4251_);
    lean_dec(v_ref_4249_);
    return v_res_4256_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(
    mut v_00_u03b1_4257_: *mut LeanObject,
    mut v_msg_4258_: *mut LeanObject,
    mut v___y_4259_: *mut LeanObject,
    mut v___y_4260_: *mut LeanObject,
    mut v___y_4261_: *mut LeanObject,
    mut v___y_4262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    v___x_4264_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
    return v___x_4264_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(
    mut v_00_u03b1_4265_: *mut LeanObject,
    mut v_msg_4266_: *mut LeanObject,
    mut v___y_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
    mut v___y_4271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4272_: *mut LeanObject = core::ptr::null_mut();
    v_res_4272_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_4265_, v_msg_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
    lean_dec(v___y_4270_);
    lean_dec_ref(v___y_4269_);
    lean_dec(v___y_4268_);
    lean_dec_ref(v___y_4267_);
    return v_res_4272_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1() -> *mut LeanObject {
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    v___x_4274_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0;
    v___x_4275_ = l_Lean_stringToMessageData(v___x_4274_);
    return v___x_4275_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_rwIfOrMatcher(
    mut v_idx_4276_: *mut LeanObject,
    mut v_e_4277_: *mut LeanObject,
    mut v_a_4278_: *mut LeanObject,
    mut v_a_4279_: *mut LeanObject,
    mut v_a_4280_: *mut LeanObject,
    mut v_a_4281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v___y_4303_: u8 = 0;
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: u8 = 0;
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
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
                lean_inc_ref(v___y_4284_);
                v___x_4285_ = l_Lean_Meta_findLocalDeclWithType_x3f(
                    v___y_4284_,
                    v_a_4278_,
                    v_a_4279_,
                    v_a_4280_,
                    v_a_4281_,
                );
                if lean_obj_tag(v___x_4285_) == 0 {
                    v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
                    lean_inc(v_a_4286_);
                    lean_dec_ref_known(v___x_4285_, 1);
                    if lean_obj_tag(v_a_4286_) == 1 {
                        lean_dec_ref(v___y_4284_);
                        v_val_4287_ = lean_ctor_get(v_a_4286_, 0);
                        lean_inc(v_val_4287_);
                        lean_dec_ref_known(v_a_4286_, 1);
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
                        lean_dec(v_a_4286_);
                        lean_dec_ref(v_e_4277_);
                        v___x_4290_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1,
                        );
                        v___x_4291_ = l_Lean_MessageData_ofExpr(v___y_4284_);
                        v___x_4292_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4292_, 0, v___x_4290_);
                        lean_ctor_set(v___x_4292_, 1, v___x_4291_);
                        v___x_4293_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_4292_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
                        return v___x_4293_;
                    }
                } else {
                    lean_dec_ref(v___y_4284_);
                    lean_dec_ref(v_e_4277_);
                    v_a_4294_ = lean_ctor_get(v___x_4285_, 0);
                    v_isSharedCheck_4301_ = (!lean_is_exclusive(v___x_4285_)) as u8;
                    if v_isSharedCheck_4301_ == 0 {
                        v___x_4296_ = v___x_4285_;
                        v_isShared_4297_ = v_isSharedCheck_4301_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4294_);
                        lean_dec(v___x_4285_);
                        v___x_4296_ = lean_box(0);
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
                    v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
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
                    v___x_4305_ = lean_unsigned_to_nat(1);
                    v___x_4306_ = l_Lean_Expr_getAppNumArgs(v_e_4277_);
                    v___x_4307_ = lean_nat_sub(v___x_4306_, v___x_4305_);
                    lean_dec(v___x_4306_);
                    v___x_4308_ = lean_nat_sub(v___x_4307_, v___x_4305_);
                    lean_dec(v___x_4307_);
                    v_c_4309_ = l_Lean_Expr_getRevArg_x21(v_e_4277_, v___x_4308_);
                    v___x_4310_ = lean_unsigned_to_nat(0);
                    v___x_4311_ = lean_nat_dec_eq(v_idx_4276_, v___x_4310_);
                    lean_dec(v_idx_4276_);
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
    mut v_idx_4317_: *mut LeanObject,
    mut v_e_4318_: *mut LeanObject,
    mut v_a_4319_: *mut LeanObject,
    mut v_a_4320_: *mut LeanObject,
    mut v_a_4321_: *mut LeanObject,
    mut v_a_4322_: *mut LeanObject,
    mut v_a_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4324_: *mut LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(
        v_idx_4317_,
        v_e_4318_,
        v_a_4319_,
        v_a_4320_,
        v_a_4321_,
        v_a_4322_,
    );
    lean_dec(v_a_4322_);
    lean_dec_ref(v_a_4321_);
    lean_dec(v_a_4320_);
    lean_dec_ref(v_a_4319_);
    return v_res_4324_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default =
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default();
    lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default);
    l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo =
        _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo();
    lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
}
