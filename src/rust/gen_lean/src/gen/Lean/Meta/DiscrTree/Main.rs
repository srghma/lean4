// Lean compiler output
// Module: Lean.Meta.DiscrTree.Main
// Imports: Lean.Meta.Basic Lean.Meta.DiscrTree.Basic Lean.Meta.WHNF
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_pop, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr,
    lean_nat_sub, lean_st_ref_get, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_isEqvAux___redArg};
use crate::r#gen::Init::Data::Array::BinSearch::l_Array_binSearchAux___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::r#gen::Lean::Class::lean_is_class;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux,
    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_constName_x21, l_Lean_Expr_etaExpandedStrict_x3f,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21,
    l_Lean_Expr_hasExprMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConst, l_Lean_Expr_isConstOf,
    l_Lean_Expr_isRawNatLit, l_Lean_Expr_sort___override, l_Lean_instBEqMVarId_beq,
    l_Lean_instInhabitedExpr, l_Lean_mkMVar,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_MVarId_isReadOnlyOrSyntheticOpaque,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey, l_Lean_Meta_ParamInfo_isImplicit,
    l_Lean_Meta_ParamInfo_isStrictImplicit, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_throwIsDefEqStuck___redArg, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    initialize_Lean_Meta_DiscrTree_Basic, l_Lean_Meta_DiscrTree_Key_lt,
    l_Lean_Meta_DiscrTree_hasNoindexAnnotation, l_Lean_Meta_DiscrTree_insertKeyValue___redArg,
    l_Lean_Meta_DiscrTree_instInhabitedTrie, l_Lean_Meta_DiscrTree_mkNoindexAnnotation,
    runtime_initialize_Lean_Meta_DiscrTree_Basic,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
    l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed,
};
use crate::r#gen::Lean::Meta::FunInfo::l_Lean_Meta_getFunInfoNArgs;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProof, l_Lean_Meta_isType};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos, l_Lean_Meta_isMatcherAppCore_x3f,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_unfoldDefinition_x3f, l_Lean_Meta_whnfCore,
    runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isRecCore;
use crate::r#gen::Lean::ReducibilityAttrs::lean_get_reducibility_status;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [95, 100, 105, 115, 99, 114, 95, 116, 114, 101, 101, 95, 116, 109, 112, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__0_value) as *mut leanh::LeanObject,8688099809373931572 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__1_value) as *mut leanh::LeanObject,13428217069302927667 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__3_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__4_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 117, 99, 99, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__6_value) as *mut leanh::LeanObject,16112798088292836701 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__0_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__1_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 100, 100, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 100, 100, 0]};
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__4_value) as *mut leanh::LeanObject,17313347264508353403 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value) as *mut leanh::LeanObject,6683391611519377970 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__3_value) as *mut leanh::LeanObject,17073733886952259026 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6_value
) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_DiscrTree_mkPath___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_DiscrTree_mkPath___closed__0: u64 = 0;
pub static l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0_value:
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
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 4,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        (((3 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3_value:
    leanh::LeanArrayObject<4> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 4,
    m_capacity: 4,
    m_data: [
        core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5_value:
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
    m_fun: l_Lean_Meta_DiscrTree_instBEqKey_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6_value:
    leanh::LeanArrayObject<1> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 1,
    m_capacity: 1,
    m_data: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3_value
) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0_value:
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
    m_fun: l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_DiscrTree_Key_arity(
    mut v_x_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3001_) {
        4 => {
            let mut v_a_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3002_ = leanh::lean_ctor_get(v_x_3001_, 1);
            leanh::lean_inc(v_a_3002_);
            return v_a_3002_;
        }
        3 => {
            let mut v_a_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3003_ = leanh::lean_ctor_get(v_x_3001_, 1);
            leanh::lean_inc(v_a_3003_);
            return v_a_3003_;
        }
        5 => {
            let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3004_ = leanh::lean_unsigned_to_nat(1);
            return v___x_3004_;
        }
        6 => {
            let mut v_a_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_3005_ = leanh::lean_ctor_get(v_x_3001_, 2);
            v___x_3006_ = leanh::lean_unsigned_to_nat(1);
            v___x_3007_ = lean_nat_add(v___x_3006_, v_a_3005_);
            return v___x_3007_;
        }
        _ => {
            let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3008_ = leanh::lean_unsigned_to_nat(0);
            return v___x_3008_;
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_Key_arity___boxed(
    mut v_x_3009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_Meta_DiscrTree_Key_arity(v_x_3009_);
    leanh::lean_dec(v_x_3009_);
    return v_res_3010_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3015_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId;
    v___x_3016_ = l_Lean_mkMVar(v___x_3015_);
    return v___x_3016_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar()
-> *mut leanh::LeanObject {
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0_once
        ),
        _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar___closed__0,
    );
    return v___x_3017_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(
    mut v_a_3018_: *mut leanh::LeanObject,
    mut v_i_3019_: *mut leanh::LeanObject,
    mut v_infos_3020_: *mut leanh::LeanObject,
    mut v_a_3021_: *mut leanh::LeanObject,
    mut v_a_3022_: *mut leanh::LeanObject,
    mut v_a_3023_: *mut leanh::LeanObject,
    mut v_a_3024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_info_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_3030_: u8 = 0;
    let mut v___y_3032_: u8 = 0;
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3037_: u8 = 0;
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v___x_3048_: u8 = 0;
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3026_ = lean_array_get_size(v_infos_3020_);
                v___x_3027_ = lean_nat_dec_lt(v_i_3019_, v___x_3026_);
                if v___x_3027_ == 0 {
                    v___x_3028_ =
                        l_Lean_Meta_isProof(v_a_3018_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
                    return v___x_3028_;
                } else {
                    v_info_3029_ = lean_array_fget_borrowed(v_infos_3020_, v_i_3019_);
                    v_isInstance_3030_ = leanh::lean_ctor_get_uint8(
                        v_info_3029_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 4) as u32,
                    );
                    if v_isInstance_3030_ == 0 {
                        v___x_3048_ = l_Lean_Meta_ParamInfo_isImplicit(v_info_3029_);
                        if v___x_3048_ == 0 {
                            v___x_3049_ = l_Lean_Meta_ParamInfo_isStrictImplicit(v_info_3029_);
                            if v___x_3049_ == 0 {
                                v___x_3050_ = l_Lean_Meta_isProof(
                                    v_a_3018_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_,
                                );
                                return v___x_3050_;
                            } else {
                                v___y_3032_ = v___x_3049_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_3032_ = v___x_3027_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_3018_);
                        v___x_3051_ = leanh::lean_box((v___x_3027_) as usize);
                        v___x_3052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3052_, 0, v___x_3051_);
                        return v___x_3052_;
                    }
                }
            }
            1 => {
                v___x_3033_ =
                    l_Lean_Meta_isType(v_a_3018_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_);
                if leanh::lean_obj_tag(v___x_3033_) == 0 {
                    v_a_3034_ = leanh::lean_ctor_get(v___x_3033_, 0);
                    v_isSharedCheck_3047_ = (!leanh::lean_is_exclusive(v___x_3033_)) as u8;
                    if v_isSharedCheck_3047_ == 0 {
                        v___x_3036_ = v___x_3033_;
                        v_isShared_3037_ = v_isSharedCheck_3047_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3034_);
                        leanh::lean_dec(v___x_3033_);
                        v___x_3036_ = leanh::lean_box(0);
                        v_isShared_3037_ = v_isSharedCheck_3047_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_3033_;
                }
            }
            2 => {
                v___x_3038_ = (leanh::lean_unbox(v_a_3034_) as u8);
                leanh::lean_dec(v_a_3034_);
                if v___x_3038_ == 0 {
                    v___x_3039_ = leanh::lean_box((v___y_3032_) as usize);
                    if v_isShared_3037_ == 0 {
                        leanh::lean_ctor_set(v___x_3036_, 0, v___x_3039_);
                        v___x_3041_ = v___x_3036_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3039_);
                        v___x_3041_ = v_reuseFailAlloc_3042_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3043_ = leanh::lean_box((v_isInstance_3030_) as usize);
                    if v_isShared_3037_ == 0 {
                        leanh::lean_ctor_set(v___x_3036_, 0, v___x_3043_);
                        v___x_3045_ = v___x_3036_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3046_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
                        v___x_3045_ = v_reuseFailAlloc_3046_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3041_;
            }
            4 => {
                return v___x_3045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg___boxed(
    mut v_a_3053_: *mut leanh::LeanObject,
    mut v_i_3054_: *mut leanh::LeanObject,
    mut v_infos_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_a_3057_: *mut leanh::LeanObject,
    mut v_a_3058_: *mut leanh::LeanObject,
    mut v_a_3059_: *mut leanh::LeanObject,
    mut v_a_3060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(
        v_a_3053_,
        v_i_3054_,
        v_infos_3055_,
        v_a_3056_,
        v_a_3057_,
        v_a_3058_,
        v_a_3059_,
    );
    leanh::lean_dec(v_a_3059_);
    leanh::lean_dec_ref(v_a_3058_);
    leanh::lean_dec(v_a_3057_);
    leanh::lean_dec_ref(v_a_3056_);
    leanh::lean_dec_ref(v_infos_3055_);
    leanh::lean_dec(v_i_3054_);
    return v_res_3061_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(
    mut v_infos_3062_: *mut leanh::LeanObject,
    mut v_x_3063_: *mut leanh::LeanObject,
    mut v_x_3064_: *mut leanh::LeanObject,
    mut v_x_3065_: *mut leanh::LeanObject,
    mut v_a_3066_: *mut leanh::LeanObject,
    mut v_a_3067_: *mut leanh::LeanObject,
    mut v_a_3068_: *mut leanh::LeanObject,
    mut v_a_3069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: u8 = 0;
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3088_: u8 = 0;
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3064_) == 5 {
                    v_fn_3071_ = leanh::lean_ctor_get(v_x_3064_, 0);
                    leanh::lean_inc_ref(v_fn_3071_);
                    v_arg_3072_ = leanh::lean_ctor_get(v_x_3064_, 1);
                    leanh::lean_inc_ref_n(v_arg_3072_, 2);
                    leanh::lean_dec_ref_known(v_x_3064_, 2);
                    v___x_3073_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_ignoreArg(
                            v_arg_3072_,
                            v_x_3063_,
                            v_infos_3062_,
                            v_a_3066_,
                            v_a_3067_,
                            v_a_3068_,
                            v_a_3069_,
                        );
                    if leanh::lean_obj_tag(v___x_3073_) == 0 {
                        v_a_3074_ = leanh::lean_ctor_get(v___x_3073_, 0);
                        leanh::lean_inc(v_a_3074_);
                        leanh::lean_dec_ref_known(v___x_3073_, 1);
                        v___x_3075_ = (leanh::lean_unbox(v_a_3074_) as u8);
                        leanh::lean_dec(v_a_3074_);
                        if v___x_3075_ == 0 {
                            v___x_3076_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3077_ = lean_nat_sub(v_x_3063_, v___x_3076_);
                            leanh::lean_dec(v_x_3063_);
                            v___x_3078_ = lean_array_push(v_x_3065_, v_arg_3072_);
                            v_x_3063_ = v___x_3077_;
                            v_x_3064_ = v_fn_3071_;
                            v_x_3065_ = v___x_3078_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_arg_3072_);
                            v___x_3080_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3081_ = lean_nat_sub(v_x_3063_, v___x_3080_);
                            leanh::lean_dec(v_x_3063_);
                            v___x_3082_ =
                                l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
                            v___x_3083_ = lean_array_push(v_x_3065_, v___x_3082_);
                            v_x_3063_ = v___x_3081_;
                            v_x_3064_ = v_fn_3071_;
                            v_x_3065_ = v___x_3083_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_3072_);
                        leanh::lean_dec_ref(v_fn_3071_);
                        leanh::lean_dec_ref(v_x_3065_);
                        leanh::lean_dec(v_x_3063_);
                        v_a_3085_ = leanh::lean_ctor_get(v___x_3073_, 0);
                        v_isSharedCheck_3092_ =
                            (!leanh::lean_is_exclusive(v___x_3073_)) as u8;
                        if v_isSharedCheck_3092_ == 0 {
                            v___x_3087_ = v___x_3073_;
                            v_isShared_3088_ = v_isSharedCheck_3092_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3085_);
                            leanh::lean_dec(v___x_3073_);
                            v___x_3087_ = leanh::lean_box(0);
                            v_isShared_3088_ = v_isSharedCheck_3092_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_3064_);
                    leanh::lean_dec(v_x_3063_);
                    v___x_3093_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3093_, 0, v_x_3065_);
                    return v___x_3093_;
                }
            }
            1 => {
                if v_isShared_3088_ == 0 {
                    v___x_3090_ = v___x_3087_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3091_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
                    v___x_3090_ = v_reuseFailAlloc_3091_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3090_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux___boxed(
    mut v_infos_3094_: *mut leanh::LeanObject,
    mut v_x_3095_: *mut leanh::LeanObject,
    mut v_x_3096_: *mut leanh::LeanObject,
    mut v_x_3097_: *mut leanh::LeanObject,
    mut v_a_3098_: *mut leanh::LeanObject,
    mut v_a_3099_: *mut leanh::LeanObject,
    mut v_a_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
    mut v_a_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3103_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(
        v_infos_3094_,
        v_x_3095_,
        v_x_3096_,
        v_x_3097_,
        v_a_3098_,
        v_a_3099_,
        v_a_3100_,
        v_a_3101_,
    );
    leanh::lean_dec(v_a_3101_);
    leanh::lean_dec_ref(v_a_3100_);
    leanh::lean_dec(v_a_3099_);
    leanh::lean_dec_ref(v_a_3098_);
    leanh::lean_dec_ref(v_infos_3094_);
    return v_res_3103_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(
    mut v_e_3118_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3119_: u8 = 0;
    let mut v___x_3120_: u8 = 0;
    let mut v_f_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v_fName_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3125_: u8 = 0;
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u8 = 0;
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: u8 = 0;
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: u8 = 0;
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: u8 = 0;
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3119_ = l_Lean_Expr_isRawNatLit(v_e_3118_);
                v___x_3120_ = 1;
                if v___x_3119_ == 0 {
                    v_f_3121_ = l_Lean_Expr_getAppFn(v_e_3118_);
                    v___x_3122_ = l_Lean_Expr_isConst(v_f_3121_);
                    if v___x_3122_ == 0 {
                        leanh::lean_dec_ref(v_f_3121_);
                        leanh::lean_dec_ref(v_e_3118_);
                        return v___x_3119_;
                    } else {
                        if v___x_3119_ == 0 {
                            v_fName_3123_ = l_Lean_Expr_constName_x21(v_f_3121_);
                            leanh::lean_dec_ref(v_f_3121_);
                            v___x_3146_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
                            v___x_3147_ = lean_name_eq(v_fName_3123_, v___x_3146_);
                            if v___x_3147_ == 0 {
                                v___y_3138_ = v___x_3147_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3148_ = l_Lean_Expr_getAppNumArgs(v_e_3118_);
                                v___x_3149_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3150_ = lean_nat_dec_eq(v___x_3148_, v___x_3149_);
                                leanh::lean_dec(v___x_3148_);
                                v___y_3138_ = v___x_3150_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_f_3121_);
                            leanh::lean_dec_ref(v_e_3118_);
                            return v___x_3119_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3118_);
                    return v___x_3120_;
                }
            }
            1 => {
                if v___y_3125_ == 0 {
                    v___x_3126_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
                    v___x_3127_ = lean_name_eq(v_fName_3123_, v___x_3126_);
                    leanh::lean_dec(v_fName_3123_);
                    if v___x_3127_ == 0 {
                        leanh::lean_dec_ref(v_e_3118_);
                        if v___x_3127_ == 0 {
                            return v___x_3127_;
                        } else {
                            return v___x_3120_;
                        }
                    } else {
                        v___x_3128_ = l_Lean_Expr_getAppNumArgs(v_e_3118_);
                        leanh::lean_dec_ref(v_e_3118_);
                        v___x_3129_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3130_ = lean_nat_dec_eq(v___x_3128_, v___x_3129_);
                        leanh::lean_dec(v___x_3128_);
                        if v___x_3130_ == 0 {
                            return v___x_3130_;
                        } else {
                            return v___x_3120_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fName_3123_);
                    v___x_3131_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3132_ = l_Lean_Expr_getAppNumArgs(v_e_3118_);
                    v___x_3133_ = lean_nat_sub(v___x_3132_, v___x_3131_);
                    leanh::lean_dec(v___x_3132_);
                    v___x_3134_ = lean_nat_sub(v___x_3133_, v___x_3131_);
                    leanh::lean_dec(v___x_3133_);
                    v___x_3135_ = l_Lean_Expr_getRevArg_x21(v_e_3118_, v___x_3134_);
                    leanh::lean_dec_ref(v_e_3118_);
                    v_e_3118_ = v___x_3135_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_3138_ == 0 {
                    v___x_3139_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5;
                    v___x_3140_ = lean_name_eq(v_fName_3123_, v___x_3139_);
                    if v___x_3140_ == 0 {
                        v___y_3125_ = v___x_3140_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3141_ = l_Lean_Expr_getAppNumArgs(v_e_3118_);
                        v___x_3142_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3143_ = lean_nat_dec_eq(v___x_3141_, v___x_3142_);
                        leanh::lean_dec(v___x_3141_);
                        v___y_3125_ = v___x_3143_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fName_3123_);
                    v___x_3144_ = l_Lean_Expr_appArg_x21(v_e_3118_);
                    leanh::lean_dec_ref(v_e_3118_);
                    v_e_3118_ = v___x_3144_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___boxed(
    mut v_e_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3152_: u8 = 0;
    let mut v_r_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(v_e_3151_);
    v_r_3153_ = leanh::lean_box((v_res_3152_) as usize);
    return v_r_3153_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(
    mut v_e_3156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3158_: u8 = 0;
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3170_: u8 = 0;
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3174_: u8 = 0;
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: u8 = 0;
    let mut v___x_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: u8 = 0;
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3204_: u8 = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: u8 = 0;
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_f_3161_ = l_Lean_Expr_getAppFn(v_e_3156_);
                match leanh::lean_obj_tag(v_f_3161_) {
                    9 => {
                        leanh::lean_dec_ref(v_e_3156_);
                        v_a_3162_ = leanh::lean_ctor_get(v_f_3161_, 0);
                        leanh::lean_inc_ref(v_a_3162_);
                        leanh::lean_dec_ref_known(v_f_3161_, 1);
                        if leanh::lean_obj_tag(v_a_3162_) == 0 {
                            v_val_3163_ = leanh::lean_ctor_get(v_a_3162_, 0);
                            v_isSharedCheck_3170_ =
                                (!leanh::lean_is_exclusive(v_a_3162_)) as u8;
                            if v_isSharedCheck_3170_ == 0 {
                                v___x_3165_ = v_a_3162_;
                                v_isShared_3166_ = v_isSharedCheck_3170_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_3163_);
                                leanh::lean_dec(v_a_3162_);
                                v___x_3165_ = leanh::lean_box(0);
                                v_isShared_3166_ = v_isSharedCheck_3170_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_a_3162_);
                            v___x_3171_ = leanh::lean_box(0);
                            return v___x_3171_;
                        }
                    }
                    4 => {
                        v_declName_3172_ = leanh::lean_ctor_get(v_f_3161_, 0);
                        leanh::lean_inc(v_declName_3172_);
                        leanh::lean_dec_ref_known(v_f_3161_, 2);
                        v___x_3205_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
                        v___x_3206_ = lean_name_eq(v_declName_3172_, v___x_3205_);
                        if v___x_3206_ == 0 {
                            v___y_3187_ = v___x_3206_;
                            state = 5;
                            continue;
                        } else {
                            v___x_3207_ = l_Lean_Expr_getAppNumArgs(v_e_3156_);
                            v___x_3208_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3209_ = lean_nat_dec_eq(v___x_3207_, v___x_3208_);
                            leanh::lean_dec(v___x_3207_);
                            v___y_3187_ = v___x_3209_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec_ref(v_f_3161_);
                        leanh::lean_dec_ref(v_e_3156_);
                        v___x_3210_ = leanh::lean_box(0);
                        return v___x_3210_;
                    }
                }
            }
            1 => {
                if v___y_3158_ == 0 {
                    v___x_3159_ = leanh::lean_box(0);
                    return v___x_3159_;
                } else {
                    v___x_3160_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop___closed__0;
                    return v___x_3160_;
                }
            }
            2 => {
                if v_isShared_3166_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3165_, 1);
                    v___x_3168_ = v___x_3165_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3169_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_val_3163_);
                    v___x_3168_ = v_reuseFailAlloc_3169_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3168_;
            }
            4 => {
                if v___y_3174_ == 0 {
                    v___x_3175_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__2;
                    v___x_3176_ = lean_name_eq(v_declName_3172_, v___x_3175_);
                    leanh::lean_dec(v_declName_3172_);
                    if v___x_3176_ == 0 {
                        leanh::lean_dec_ref(v_e_3156_);
                        v___y_3158_ = v___x_3176_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3177_ = l_Lean_Expr_getAppNumArgs(v_e_3156_);
                        leanh::lean_dec_ref(v_e_3156_);
                        v___x_3178_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3179_ = lean_nat_dec_eq(v___x_3177_, v___x_3178_);
                        leanh::lean_dec(v___x_3177_);
                        v___y_3158_ = v___x_3179_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_3172_);
                    v___x_3180_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3181_ = l_Lean_Expr_getAppNumArgs(v_e_3156_);
                    v___x_3182_ = lean_nat_sub(v___x_3181_, v___x_3180_);
                    leanh::lean_dec(v___x_3181_);
                    v___x_3183_ = lean_nat_sub(v___x_3182_, v___x_3180_);
                    leanh::lean_dec(v___x_3182_);
                    v___x_3184_ = l_Lean_Expr_getRevArg_x21(v_e_3156_, v___x_3183_);
                    leanh::lean_dec_ref(v_e_3156_);
                    v_e_3156_ = v___x_3184_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                if v___y_3187_ == 0 {
                    v___x_3188_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__5;
                    v___x_3189_ = lean_name_eq(v_declName_3172_, v___x_3188_);
                    if v___x_3189_ == 0 {
                        v___y_3174_ = v___x_3189_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3190_ = l_Lean_Expr_getAppNumArgs(v_e_3156_);
                        v___x_3191_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3192_ = lean_nat_dec_eq(v___x_3190_, v___x_3191_);
                        leanh::lean_dec(v___x_3190_);
                        v___y_3174_ = v___x_3192_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_3172_);
                    v___x_3193_ = l_Lean_Expr_appArg_x21(v_e_3156_);
                    leanh::lean_dec_ref(v_e_3156_);
                    v___x_3194_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v___x_3193_);
                    if leanh::lean_obj_tag(v___x_3194_) == 0 {
                        return v___x_3194_;
                    } else {
                        v_val_3195_ = leanh::lean_ctor_get(v___x_3194_, 0);
                        v_isSharedCheck_3204_ =
                            (!leanh::lean_is_exclusive(v___x_3194_)) as u8;
                        if v_isSharedCheck_3204_ == 0 {
                            v___x_3197_ = v___x_3194_;
                            v_isShared_3198_ = v_isSharedCheck_3204_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3195_);
                            leanh::lean_dec(v___x_3194_);
                            v___x_3197_ = leanh::lean_box(0);
                            v_isShared_3198_ = v_isSharedCheck_3204_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_3199_ = leanh::lean_unsigned_to_nat(1);
                v___x_3200_ = lean_nat_add(v_val_3195_, v___x_3199_);
                leanh::lean_dec(v_val_3195_);
                if v_isShared_3198_ == 0 {
                    leanh::lean_ctor_set(v___x_3197_, 0, v___x_3200_);
                    v___x_3202_ = v___x_3197_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
                    v___x_3202_ = v_reuseFailAlloc_3203_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(
    mut v_e_3211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_3211_);
                v___x_3212_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(
                    v_e_3211_,
                );
                if v___x_3212_ == 0 {
                    leanh::lean_dec_ref(v_e_3211_);
                    v___x_3213_ = leanh::lean_box(0);
                    return v___x_3213_;
                } else {
                    v___x_3214_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f_loop(v_e_3211_);
                    if leanh::lean_obj_tag(v___x_3214_) == 1 {
                        v_val_3215_ = leanh::lean_ctor_get(v___x_3214_, 0);
                        v_isSharedCheck_3223_ =
                            (!leanh::lean_is_exclusive(v___x_3214_)) as u8;
                        if v_isSharedCheck_3223_ == 0 {
                            v___x_3217_ = v___x_3214_;
                            v_isShared_3218_ = v_isSharedCheck_3223_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3215_);
                            leanh::lean_dec(v___x_3214_);
                            v___x_3217_ = leanh::lean_box(0);
                            v_isShared_3218_ = v_isSharedCheck_3223_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3214_);
                        v___x_3224_ = leanh::lean_box(0);
                        return v___x_3224_;
                    }
                }
            }
            1 => {
                v___x_3219_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3219_, 0, v_val_3215_);
                if v_isShared_3218_ == 0 {
                    leanh::lean_ctor_set(v___x_3217_, 0, v___x_3219_);
                    v___x_3221_ = v___x_3217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(
    mut v_e_3227_: *mut leanh::LeanObject,
    mut v_a_3228_: *mut leanh::LeanObject,
    mut v_a_3229_: *mut leanh::LeanObject,
    mut v_a_3230_: *mut leanh::LeanObject,
    mut v_a_3231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3244_: u8 = 0;
    let mut v_a_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_3231_);
                leanh::lean_inc_ref(v_a_3230_);
                leanh::lean_inc(v_a_3229_);
                leanh::lean_inc_ref(v_a_3228_);
                v___x_3233_ = lean_whnf(v_e_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
                if leanh::lean_obj_tag(v___x_3233_) == 0 {
                    v_a_3234_ = leanh::lean_ctor_get(v___x_3233_, 0);
                    v_isSharedCheck_3244_ = (!leanh::lean_is_exclusive(v___x_3233_)) as u8;
                    if v_isSharedCheck_3244_ == 0 {
                        v___x_3236_ = v___x_3233_;
                        v_isShared_3237_ = v_isSharedCheck_3244_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3234_);
                        leanh::lean_dec(v___x_3233_);
                        v___x_3236_ = leanh::lean_box(0);
                        v_isShared_3237_ = v_isSharedCheck_3244_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3245_ = leanh::lean_ctor_get(v___x_3233_, 0);
                    v_isSharedCheck_3252_ = (!leanh::lean_is_exclusive(v___x_3233_)) as u8;
                    if v_isSharedCheck_3252_ == 0 {
                        v___x_3247_ = v___x_3233_;
                        v_isShared_3248_ = v_isSharedCheck_3252_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3245_);
                        leanh::lean_dec(v___x_3233_);
                        v___x_3247_ = leanh::lean_box(0);
                        v_isShared_3248_ = v_isSharedCheck_3252_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3238_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___closed__0;
                v___x_3239_ = l_Lean_Expr_isConstOf(v_a_3234_, v___x_3238_);
                leanh::lean_dec(v_a_3234_);
                v___x_3240_ = leanh::lean_box((v___x_3239_) as usize);
                if v_isShared_3237_ == 0 {
                    leanh::lean_ctor_set(v___x_3236_, 0, v___x_3240_);
                    v___x_3242_ = v___x_3236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3243_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
                    v___x_3242_ = v_reuseFailAlloc_3243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3242_;
            }
            3 => {
                if v_isShared_3248_ == 0 {
                    v___x_3250_ = v___x_3247_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
                    v___x_3250_ = v_reuseFailAlloc_3251_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType___boxed(
    mut v_e_3253_: *mut leanh::LeanObject,
    mut v_a_3254_: *mut leanh::LeanObject,
    mut v_a_3255_: *mut leanh::LeanObject,
    mut v_a_3256_: *mut leanh::LeanObject,
    mut v_a_3257_: *mut leanh::LeanObject,
    mut v_a_3258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3259_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(
        v_e_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_,
    );
    leanh::lean_dec(v_a_3257_);
    leanh::lean_dec_ref(v_a_3256_);
    leanh::lean_dec(v_a_3255_);
    leanh::lean_dec_ref(v_a_3254_);
    return v_res_3259_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(
    mut v_fName_3273_: *mut leanh::LeanObject,
    mut v_e_3274_: *mut leanh::LeanObject,
    mut v_a_3275_: *mut leanh::LeanObject,
    mut v_a_3276_: *mut leanh::LeanObject,
    mut v_a_3277_: *mut leanh::LeanObject,
    mut v_a_3278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3281_: u8 = 0;
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: u8 = 0;
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: u8 = 0;
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v_unused_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3311_: u8 = 0;
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: u8 = 0;
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: u8 = 0;
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3333_: u8 = 0;
    let mut v_unused_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3336_: u8 = 0;
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3346_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__6;
                v___x_3347_ = lean_name_eq(v_fName_3273_, v___x_3346_);
                if v___x_3347_ == 0 {
                    v___y_3336_ = v___x_3347_;
                    state = 7;
                    continue;
                } else {
                    v___x_3348_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
                    v___x_3349_ = leanh::lean_unsigned_to_nat(2);
                    v___x_3350_ = lean_nat_dec_eq(v___x_3348_, v___x_3349_);
                    leanh::lean_dec(v___x_3348_);
                    v___y_3336_ = v___x_3350_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_3281_ == 0 {
                    v___x_3282_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral___closed__7;
                    v___x_3283_ = lean_name_eq(v_fName_3273_, v___x_3282_);
                    if v___x_3283_ == 0 {
                        v___x_3284_ = leanh::lean_box((v___x_3283_) as usize);
                        v___x_3285_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3285_, 0, v___x_3284_);
                        return v___x_3285_;
                    } else {
                        v___x_3286_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
                        v___x_3287_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3288_ = lean_nat_dec_eq(v___x_3286_, v___x_3287_);
                        leanh::lean_dec(v___x_3286_);
                        v___x_3289_ = leanh::lean_box((v___x_3288_) as usize);
                        v___x_3290_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3290_, 0, v___x_3289_);
                        return v___x_3290_;
                    }
                } else {
                    v___x_3291_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3292_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
                    v___x_3293_ = lean_nat_sub(v___x_3292_, v___x_3291_);
                    leanh::lean_dec(v___x_3292_);
                    v___x_3294_ = lean_nat_sub(v___x_3293_, v___x_3291_);
                    leanh::lean_dec(v___x_3293_);
                    v___x_3295_ = l_Lean_Expr_getRevArg_x21(v_e_3274_, v___x_3294_);
                    v___x_3296_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(
                            v___x_3295_,
                            v_a_3275_,
                            v_a_3276_,
                            v_a_3277_,
                            v_a_3278_,
                        );
                    if leanh::lean_obj_tag(v___x_3296_) == 0 {
                        v_a_3297_ = leanh::lean_ctor_get(v___x_3296_, 0);
                        leanh::lean_inc(v_a_3297_);
                        v___x_3298_ = (leanh::lean_unbox(v_a_3297_) as u8);
                        leanh::lean_dec(v_a_3297_);
                        if v___x_3298_ == 0 {
                            return v___x_3296_;
                        } else {
                            v_isSharedCheck_3308_ =
                                (!leanh::lean_is_exclusive(v___x_3296_)) as u8;
                            if v_isSharedCheck_3308_ == 0 {
                                v_unused_3309_ = leanh::lean_ctor_get(v___x_3296_, 0);
                                leanh::lean_dec(v_unused_3309_);
                                v___x_3300_ = v___x_3296_;
                                v_isShared_3301_ = v_isSharedCheck_3308_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3296_);
                                v___x_3300_ = leanh::lean_box(0);
                                v_isShared_3301_ = v_isSharedCheck_3308_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        return v___x_3296_;
                    }
                }
            }
            2 => {
                v___x_3302_ = l_Lean_Expr_appArg_x21(v_e_3274_);
                v___x_3303_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(
                    v___x_3302_,
                );
                v___x_3304_ = leanh::lean_box((v___x_3303_) as usize);
                if v_isShared_3301_ == 0 {
                    leanh::lean_ctor_set(v___x_3300_, 0, v___x_3304_);
                    v___x_3306_ = v___x_3300_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3306_;
            }
            4 => {
                if v___y_3311_ == 0 {
                    v___x_3312_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__2;
                    v___x_3313_ = lean_name_eq(v_fName_3273_, v___x_3312_);
                    if v___x_3313_ == 0 {
                        v___y_3281_ = v___x_3313_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3314_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
                        v___x_3315_ = leanh::lean_unsigned_to_nat(6);
                        v___x_3316_ = lean_nat_dec_eq(v___x_3314_, v___x_3315_);
                        leanh::lean_dec(v___x_3314_);
                        v___y_3281_ = v___x_3316_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3317_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
                    v___x_3318_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3319_ = lean_nat_sub(v___x_3317_, v___x_3318_);
                    leanh::lean_dec(v___x_3317_);
                    v___x_3320_ = l_Lean_Expr_getRevArg_x21(v_e_3274_, v___x_3319_);
                    v___x_3321_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNatType(
                            v___x_3320_,
                            v_a_3275_,
                            v_a_3276_,
                            v_a_3277_,
                            v_a_3278_,
                        );
                    if leanh::lean_obj_tag(v___x_3321_) == 0 {
                        v_a_3322_ = leanh::lean_ctor_get(v___x_3321_, 0);
                        leanh::lean_inc(v_a_3322_);
                        v___x_3323_ = (leanh::lean_unbox(v_a_3322_) as u8);
                        leanh::lean_dec(v_a_3322_);
                        if v___x_3323_ == 0 {
                            return v___x_3321_;
                        } else {
                            v_isSharedCheck_3333_ =
                                (!leanh::lean_is_exclusive(v___x_3321_)) as u8;
                            if v_isSharedCheck_3333_ == 0 {
                                v_unused_3334_ = leanh::lean_ctor_get(v___x_3321_, 0);
                                leanh::lean_dec(v_unused_3334_);
                                v___x_3325_ = v___x_3321_;
                                v_isShared_3326_ = v_isSharedCheck_3333_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3321_);
                                v___x_3325_ = leanh::lean_box(0);
                                v_isShared_3326_ = v_isSharedCheck_3333_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        return v___x_3321_;
                    }
                }
            }
            5 => {
                v___x_3327_ = l_Lean_Expr_appArg_x21(v_e_3274_);
                v___x_3328_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(
                    v___x_3327_,
                );
                v___x_3329_ = leanh::lean_box((v___x_3328_) as usize);
                if v_isShared_3326_ == 0 {
                    leanh::lean_ctor_set(v___x_3325_, 0, v___x_3329_);
                    v___x_3331_ = v___x_3325_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3332_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
                    v___x_3331_ = v_reuseFailAlloc_3332_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3331_;
            }
            7 => {
                if v___y_3336_ == 0 {
                    v___x_3337_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___closed__5;
                    v___x_3338_ = lean_name_eq(v_fName_3273_, v___x_3337_);
                    if v___x_3338_ == 0 {
                        v___y_3311_ = v___x_3338_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3339_ = l_Lean_Expr_getAppNumArgs(v_e_3274_);
                        v___x_3340_ = leanh::lean_unsigned_to_nat(4);
                        v___x_3341_ = lean_nat_dec_eq(v___x_3339_, v___x_3340_);
                        leanh::lean_dec(v___x_3339_);
                        v___y_3311_ = v___x_3341_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3342_ = l_Lean_Expr_appArg_x21(v_e_3274_);
                    v___x_3343_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isNumeral(
                            v___x_3342_,
                        );
                    v___x_3344_ = leanh::lean_box((v___x_3343_) as usize);
                    v___x_3345_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3345_, 0, v___x_3344_);
                    return v___x_3345_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset___boxed(
    mut v_fName_3351_: *mut leanh::LeanObject,
    mut v_e_3352_: *mut leanh::LeanObject,
    mut v_a_3353_: *mut leanh::LeanObject,
    mut v_a_3354_: *mut leanh::LeanObject,
    mut v_a_3355_: *mut leanh::LeanObject,
    mut v_a_3356_: *mut leanh::LeanObject,
    mut v_a_3357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3358_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(
        v_fName_3351_,
        v_e_3352_,
        v_a_3353_,
        v_a_3354_,
        v_a_3355_,
        v_a_3356_,
    );
    leanh::lean_dec(v_a_3356_);
    leanh::lean_dec_ref(v_a_3355_);
    leanh::lean_dec(v_a_3354_);
    leanh::lean_dec_ref(v_a_3353_);
    leanh::lean_dec_ref(v_e_3352_);
    leanh::lean_dec(v_fName_3351_);
    return v_res_3358_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(
    mut v_fName_3359_: *mut leanh::LeanObject,
    mut v_e_3360_: *mut leanh::LeanObject,
    mut v_a_3361_: *mut leanh::LeanObject,
    mut v_a_3362_: *mut leanh::LeanObject,
    mut v_a_3363_: *mut leanh::LeanObject,
    mut v_a_3364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3366_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(
        v_fName_3359_,
        v_e_3360_,
        v_a_3361_,
        v_a_3362_,
        v_a_3363_,
        v_a_3364_,
    );
    return v___x_3366_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar___boxed(
    mut v_fName_3367_: *mut leanh::LeanObject,
    mut v_e_3368_: *mut leanh::LeanObject,
    mut v_a_3369_: *mut leanh::LeanObject,
    mut v_a_3370_: *mut leanh::LeanObject,
    mut v_a_3371_: *mut leanh::LeanObject,
    mut v_a_3372_: *mut leanh::LeanObject,
    mut v_a_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3374_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_shouldAddAsStar(
        v_fName_3367_,
        v_e_3368_,
        v_a_3369_,
        v_a_3370_,
        v_a_3371_,
        v_a_3372_,
    );
    leanh::lean_dec(v_a_3372_);
    leanh::lean_dec_ref(v_a_3371_);
    leanh::lean_dec(v_a_3370_);
    leanh::lean_dec_ref(v_a_3369_);
    leanh::lean_dec_ref(v_e_3368_);
    leanh::lean_dec(v_fName_3367_);
    return v_res_3374_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_reduce(
    mut v_e_3375_: *mut leanh::LeanObject,
    mut v_a_3376_: *mut leanh::LeanObject,
    mut v_a_3377_: *mut leanh::LeanObject,
    mut v_a_3378_: *mut leanh::LeanObject,
    mut v_a_3379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3388_: u8 = 0;
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3397_: u8 = 0;
    let mut v_a_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3405_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3381_ =
                    l_Lean_Meta_whnfCore(v_e_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
                if leanh::lean_obj_tag(v___x_3381_) == 0 {
                    v_a_3382_ = leanh::lean_ctor_get(v___x_3381_, 0);
                    leanh::lean_inc_n(v_a_3382_, 2);
                    leanh::lean_dec_ref_known(v___x_3381_, 1);
                    v___x_3383_ = 0;
                    v___x_3384_ = l_Lean_Meta_unfoldDefinition_x3f(
                        v_a_3382_,
                        v___x_3383_,
                        v_a_3376_,
                        v_a_3377_,
                        v_a_3378_,
                        v_a_3379_,
                    );
                    if leanh::lean_obj_tag(v___x_3384_) == 0 {
                        v_a_3385_ = leanh::lean_ctor_get(v___x_3384_, 0);
                        v_isSharedCheck_3397_ =
                            (!leanh::lean_is_exclusive(v___x_3384_)) as u8;
                        if v_isSharedCheck_3397_ == 0 {
                            v___x_3387_ = v___x_3384_;
                            v_isShared_3388_ = v_isSharedCheck_3397_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3385_);
                            leanh::lean_dec(v___x_3384_);
                            v___x_3387_ = leanh::lean_box(0);
                            v_isShared_3388_ = v_isSharedCheck_3397_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3382_);
                        v_a_3398_ = leanh::lean_ctor_get(v___x_3384_, 0);
                        v_isSharedCheck_3405_ =
                            (!leanh::lean_is_exclusive(v___x_3384_)) as u8;
                        if v_isSharedCheck_3405_ == 0 {
                            v___x_3400_ = v___x_3384_;
                            v_isShared_3401_ = v_isSharedCheck_3405_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3398_);
                            leanh::lean_dec(v___x_3384_);
                            v___x_3400_ = leanh::lean_box(0);
                            v_isShared_3401_ = v_isSharedCheck_3405_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_3381_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3385_) == 0 {
                    leanh::lean_inc(v_a_3382_);
                    v___x_3389_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_3382_);
                    if leanh::lean_obj_tag(v___x_3389_) == 0 {
                        if v_isShared_3388_ == 0 {
                            leanh::lean_ctor_set(v___x_3387_, 0, v_a_3382_);
                            v___x_3391_ = v___x_3387_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3392_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3382_);
                            v___x_3391_ = v_reuseFailAlloc_3392_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3387_);
                        leanh::lean_dec(v_a_3382_);
                        v_val_3393_ = leanh::lean_ctor_get(v___x_3389_, 0);
                        leanh::lean_inc(v_val_3393_);
                        leanh::lean_dec_ref_known(v___x_3389_, 1);
                        v_e_3375_ = v_val_3393_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3387_);
                    leanh::lean_dec(v_a_3382_);
                    v_val_3395_ = leanh::lean_ctor_get(v_a_3385_, 0);
                    leanh::lean_inc(v_val_3395_);
                    leanh::lean_dec_ref_known(v_a_3385_, 1);
                    v_e_3375_ = v_val_3395_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_3391_;
            }
            3 => {
                if v_isShared_3401_ == 0 {
                    v___x_3403_ = v___x_3400_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
                    v___x_3403_ = v_reuseFailAlloc_3404_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_reduce___boxed(
    mut v_e_3406_: *mut leanh::LeanObject,
    mut v_a_3407_: *mut leanh::LeanObject,
    mut v_a_3408_: *mut leanh::LeanObject,
    mut v_a_3409_: *mut leanh::LeanObject,
    mut v_a_3410_: *mut leanh::LeanObject,
    mut v_a_3411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3412_ =
        l_Lean_Meta_DiscrTree_reduce(v_e_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_);
    leanh::lean_dec(v_a_3410_);
    leanh::lean_dec_ref(v_a_3409_);
    leanh::lean_dec(v_a_3408_);
    leanh::lean_dec_ref(v_a_3407_);
    return v_res_3412_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(
    mut v_fn_3413_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_fn_3413_) {
        9 => {
            let mut v___x_3414_: u8 = 0;
            v___x_3414_ = 0;
            return v___x_3414_;
        }
        4 => {
            let mut v___x_3415_: u8 = 0;
            v___x_3415_ = 0;
            return v___x_3415_;
        }
        1 => {
            let mut v___x_3416_: u8 = 0;
            v___x_3416_ = 0;
            return v___x_3416_;
        }
        11 => {
            let mut v___x_3417_: u8 = 0;
            v___x_3417_ = 0;
            return v___x_3417_;
        }
        7 => {
            let mut v___x_3418_: u8 = 0;
            v___x_3418_ = 0;
            return v___x_3418_;
        }
        _ => {
            let mut v___x_3419_: u8 = 0;
            v___x_3419_ = 1;
            return v___x_3419_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey___boxed(
    mut v_fn_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3421_: u8 = 0;
    let mut v_r_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(v_fn_3420_);
    leanh::lean_dec_ref(v_fn_3420_);
    v_r_3422_ = leanh::lean_box((v_res_3421_) as usize);
    return v_r_3422_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(
    mut v_e_3423_: *mut leanh::LeanObject,
    mut v_a_3424_: *mut leanh::LeanObject,
    mut v_a_3425_: *mut leanh::LeanObject,
    mut v_a_3426_: *mut leanh::LeanObject,
    mut v_a_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: u8 = 0;
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3436_: u8 = 0;
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_a_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3429_ =
                    l_Lean_Meta_whnfCore(v_e_3423_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
                if leanh::lean_obj_tag(v___x_3429_) == 0 {
                    v_a_3430_ = leanh::lean_ctor_get(v___x_3429_, 0);
                    leanh::lean_inc_n(v_a_3430_, 2);
                    leanh::lean_dec_ref_known(v___x_3429_, 1);
                    v___x_3431_ = 0;
                    v___x_3432_ = l_Lean_Meta_unfoldDefinition_x3f(
                        v_a_3430_,
                        v___x_3431_,
                        v_a_3424_,
                        v_a_3425_,
                        v_a_3426_,
                        v_a_3427_,
                    );
                    if leanh::lean_obj_tag(v___x_3432_) == 0 {
                        v_a_3433_ = leanh::lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3447_ =
                            (!leanh::lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3447_ == 0 {
                            v___x_3435_ = v___x_3432_;
                            v_isShared_3436_ = v_isSharedCheck_3447_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3433_);
                            leanh::lean_dec(v___x_3432_);
                            v___x_3435_ = leanh::lean_box(0);
                            v_isShared_3436_ = v_isSharedCheck_3447_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3430_);
                        v_a_3448_ = leanh::lean_ctor_get(v___x_3432_, 0);
                        v_isSharedCheck_3455_ =
                            (!leanh::lean_is_exclusive(v___x_3432_)) as u8;
                        if v_isSharedCheck_3455_ == 0 {
                            v___x_3450_ = v___x_3432_;
                            v_isShared_3451_ = v_isSharedCheck_3455_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3448_);
                            leanh::lean_dec(v___x_3432_);
                            v___x_3450_ = leanh::lean_box(0);
                            v_isShared_3451_ = v_isSharedCheck_3455_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v___x_3429_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3433_) == 0 {
                    if v_isShared_3436_ == 0 {
                        leanh::lean_ctor_set(v___x_3435_, 0, v_a_3430_);
                        v___x_3438_ = v___x_3435_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3439_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3430_);
                        v___x_3438_ = v_reuseFailAlloc_3439_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3440_ = leanh::lean_ctor_get(v_a_3433_, 0);
                    leanh::lean_inc(v_val_3440_);
                    leanh::lean_dec_ref_known(v_a_3433_, 1);
                    v___x_3441_ = l_Lean_Expr_getAppFn(v_val_3440_);
                    v___x_3442_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isBadKey(
                            v___x_3441_,
                        );
                    leanh::lean_dec_ref(v___x_3441_);
                    if v___x_3442_ == 0 {
                        leanh::lean_del_object(v___x_3435_);
                        leanh::lean_dec(v_a_3430_);
                        v_e_3423_ = v_val_3440_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_3440_);
                        if v_isShared_3436_ == 0 {
                            leanh::lean_ctor_set(v___x_3435_, 0, v_a_3430_);
                            v___x_3445_ = v___x_3435_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3446_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3430_);
                            v___x_3445_ = v_reuseFailAlloc_3446_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3438_;
            }
            3 => {
                return v___x_3445_;
            }
            4 => {
                if v_isShared_3451_ == 0 {
                    v___x_3453_ = v___x_3450_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v_a_3448_);
                    v___x_3453_ = v_reuseFailAlloc_3454_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step___boxed(
    mut v_e_3456_: *mut leanh::LeanObject,
    mut v_a_3457_: *mut leanh::LeanObject,
    mut v_a_3458_: *mut leanh::LeanObject,
    mut v_a_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3462_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(
            v_e_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_,
        );
    leanh::lean_dec(v_a_3460_);
    leanh::lean_dec_ref(v_a_3459_);
    leanh::lean_dec(v_a_3458_);
    leanh::lean_dec_ref(v_a_3457_);
    return v_res_3462_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(
    mut v_e_3463_: *mut leanh::LeanObject,
    mut v_a_3464_: *mut leanh::LeanObject,
    mut v_a_3465_: *mut leanh::LeanObject,
    mut v_a_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3469_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey_step(v_e_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
                if leanh::lean_obj_tag(v___x_3469_) == 0 {
                    v_a_3470_ = leanh::lean_ctor_get(v___x_3469_, 0);
                    leanh::lean_inc(v_a_3470_);
                    v___x_3471_ = l_Lean_Expr_etaExpandedStrict_x3f(v_a_3470_);
                    if leanh::lean_obj_tag(v___x_3471_) == 0 {
                        return v___x_3469_;
                    } else {
                        leanh::lean_dec_ref_known(v___x_3469_, 1);
                        v_val_3472_ = leanh::lean_ctor_get(v___x_3471_, 0);
                        leanh::lean_inc(v_val_3472_);
                        leanh::lean_dec_ref_known(v___x_3471_, 1);
                        v_e_3463_ = v_val_3472_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v___x_3469_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey___boxed(
    mut v_e_3474_: *mut leanh::LeanObject,
    mut v_a_3475_: *mut leanh::LeanObject,
    mut v_a_3476_: *mut leanh::LeanObject,
    mut v_a_3477_: *mut leanh::LeanObject,
    mut v_a_3478_: *mut leanh::LeanObject,
    mut v_a_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(
        v_e_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_,
    );
    leanh::lean_dec(v_a_3478_);
    leanh::lean_dec_ref(v_a_3477_);
    leanh::lean_dec(v_a_3476_);
    leanh::lean_dec_ref(v_a_3475_);
    return v_res_3480_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_reduceDT(
    mut v_e_3481_: *mut leanh::LeanObject,
    mut v_root_3482_: u8,
    mut v_a_3483_: *mut leanh::LeanObject,
    mut v_a_3484_: *mut leanh::LeanObject,
    mut v_a_3485_: *mut leanh::LeanObject,
    mut v_a_3486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_root_3482_ == 0 {
        let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3488_ =
            l_Lean_Meta_DiscrTree_reduce(v_e_3481_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
        return v___x_3488_;
    } else {
        let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3489_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_reduceUntilBadKey(
            v_e_3481_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_,
        );
        return v___x_3489_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_reduceDT___boxed(
    mut v_e_3490_: *mut leanh::LeanObject,
    mut v_root_3491_: *mut leanh::LeanObject,
    mut v_a_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
    mut v_a_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
    mut v_a_3496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_boxed_3497_: u8 = 0;
    let mut v_res_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_boxed_3497_ = (leanh::lean_unbox(v_root_3491_) as u8);
    v_res_3498_ = l_Lean_Meta_DiscrTree_reduceDT(
        v_e_3490_,
        v_root_boxed_3497_,
        v_a_3492_,
        v_a_3493_,
        v_a_3494_,
        v_a_3495_,
    );
    leanh::lean_dec(v_a_3495_);
    leanh::lean_dec_ref(v_a_3494_);
    leanh::lean_dec(v_a_3493_);
    leanh::lean_dec_ref(v_a_3492_);
    return v_res_3498_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(
    mut v_n_3499_: *mut leanh::LeanObject,
    mut v_todo_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3502_: u8 = 0;
    let mut v_one_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3501_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3502_ = lean_nat_dec_eq(v_n_3499_, v_zero_3501_);
                if v_isZero_3502_ == 1 {
                    leanh::lean_dec(v_n_3499_);
                    return v_todo_3500_;
                } else {
                    v_one_3503_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3504_ = lean_nat_sub(v_n_3499_, v_one_3503_);
                    leanh::lean_dec(v_n_3499_);
                    v___x_3505_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar;
                    v___x_3506_ = lean_array_push(v_todo_3500_, v___x_3505_);
                    v_n_3499_ = v_n_3504_;
                    v_todo_3500_ = v___x_3506_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(
    mut v_root_3508_: u8,
    mut v_todo_3509_: *mut leanh::LeanObject,
    mut v_e_3510_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3511_: u8,
    mut v_a_3512_: *mut leanh::LeanObject,
    mut v_a_3513_: *mut leanh::LeanObject,
    mut v_a_3514_: *mut leanh::LeanObject,
    mut v_a_3515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3527_: u8 = 0;
    let mut v_v_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3563_: u8 = 0;
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3567_: u8 = 0;
    let mut v_a_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut v_a_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_typeName_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: u8 = 0;
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: u8 = 0;
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3621_: u8 = 0;
    let mut v___x_3622_: u8 = 0;
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3633_: u8 = 0;
    let mut v_a_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3522_ = l_Lean_Meta_DiscrTree_hasNoindexAnnotation(v_e_3510_);
                if v___x_3522_ == 0 {
                    v___x_3523_ = l_Lean_Meta_DiscrTree_reduceDT(
                        v_e_3510_,
                        v_root_3508_,
                        v_a_3512_,
                        v_a_3513_,
                        v_a_3514_,
                        v_a_3515_,
                    );
                    if leanh::lean_obj_tag(v___x_3523_) == 0 {
                        v_a_3524_ = leanh::lean_ctor_get(v___x_3523_, 0);
                        v_isSharedCheck_3653_ =
                            (!leanh::lean_is_exclusive(v___x_3523_)) as u8;
                        if v_isSharedCheck_3653_ == 0 {
                            v___x_3526_ = v___x_3523_;
                            v_isShared_3527_ = v_isSharedCheck_3653_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3524_);
                            leanh::lean_dec(v___x_3523_);
                            v___x_3526_ = leanh::lean_box(0);
                            v_isShared_3527_ = v_isSharedCheck_3653_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_todo_3509_);
                        v_a_3654_ = leanh::lean_ctor_get(v___x_3523_, 0);
                        v_isSharedCheck_3661_ =
                            (!leanh::lean_is_exclusive(v___x_3523_)) as u8;
                        if v_isSharedCheck_3661_ == 0 {
                            v___x_3656_ = v___x_3523_;
                            v_isShared_3657_ = v_isSharedCheck_3661_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3654_);
                            leanh::lean_dec(v___x_3523_);
                            v___x_3656_ = leanh::lean_box(0);
                            v_isShared_3657_ = v_isSharedCheck_3661_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3510_);
                    v___x_3662_ = leanh::lean_box(0);
                    v___x_3663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3663_, 0, v___x_3662_);
                    leanh::lean_ctor_set(v___x_3663_, 1, v_todo_3509_);
                    v___x_3664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3664_, 0, v___x_3663_);
                    return v___x_3664_;
                }
            }
            1 => {
                v___x_3520_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3520_, 0, v___y_3518_);
                leanh::lean_ctor_set(v___x_3520_, 1, v_todo_3519_);
                v___x_3521_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3521_, 0, v___x_3520_);
                return v___x_3521_;
            }
            2 => {
                v___x_3535_ = l_Lean_Expr_getAppFn(v_a_3524_);
                match leanh::lean_obj_tag(v___x_3535_) {
                    9 => {
                        leanh::lean_dec(v_a_3524_);
                        v_a_3568_ = leanh::lean_ctor_get(v___x_3535_, 0);
                        leanh::lean_inc_ref(v_a_3568_);
                        leanh::lean_dec_ref_known(v___x_3535_, 1);
                        v_v_3529_ = v_a_3568_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        v_declName_3569_ = leanh::lean_ctor_get(v___x_3535_, 0);
                        leanh::lean_inc(v_declName_3569_);
                        if v_root_3508_ == 0 {
                            leanh::lean_inc(v_a_3524_);
                            v___x_3577_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(v_a_3524_);
                            if leanh::lean_obj_tag(v___x_3577_) == 1 {
                                leanh::lean_dec_ref_known(v___x_3535_, 2);
                                leanh::lean_dec(v_declName_3569_);
                                leanh::lean_dec(v_a_3524_);
                                v_val_3578_ = leanh::lean_ctor_get(v___x_3577_, 0);
                                leanh::lean_inc(v_val_3578_);
                                leanh::lean_dec_ref_known(v___x_3577_, 1);
                                v_v_3529_ = v_val_3578_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3577_);
                                leanh::lean_del_object(v___x_3526_);
                                v___x_3579_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_isOffset(v_declName_3569_, v_a_3524_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_);
                                if leanh::lean_obj_tag(v___x_3579_) == 0 {
                                    v_a_3580_ = leanh::lean_ctor_get(v___x_3579_, 0);
                                    v_isSharedCheck_3590_ =
                                        (!leanh::lean_is_exclusive(v___x_3579_)) as u8;
                                    if v_isSharedCheck_3590_ == 0 {
                                        v___x_3582_ = v___x_3579_;
                                        v_isShared_3583_ = v_isSharedCheck_3590_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3580_);
                                        leanh::lean_dec(v___x_3579_);
                                        v___x_3582_ = leanh::lean_box(0);
                                        v_isShared_3583_ = v_isSharedCheck_3590_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v___x_3535_, 2);
                                    leanh::lean_dec(v_declName_3569_);
                                    leanh::lean_dec(v_a_3524_);
                                    leanh::lean_dec_ref(v_todo_3509_);
                                    v_a_3591_ = leanh::lean_ctor_get(v___x_3579_, 0);
                                    v_isSharedCheck_3598_ =
                                        (!leanh::lean_is_exclusive(v___x_3579_)) as u8;
                                    if v_isSharedCheck_3598_ == 0 {
                                        v___x_3593_ = v___x_3579_;
                                        v_isShared_3594_ = v_isSharedCheck_3598_;
                                        state = 13;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3591_);
                                        leanh::lean_dec(v___x_3579_);
                                        v___x_3593_ = leanh::lean_box(0);
                                        v_isShared_3594_ = v_isSharedCheck_3598_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3526_);
                            v___y_3571_ = v_a_3512_;
                            v___y_3572_ = v_a_3513_;
                            v___y_3573_ = v_a_3514_;
                            v___y_3574_ = v_a_3515_;
                            state = 10;
                            continue;
                        }
                    }
                    11 => {
                        leanh::lean_del_object(v___x_3526_);
                        v_typeName_3599_ = leanh::lean_ctor_get(v___x_3535_, 0);
                        leanh::lean_inc_n(v_typeName_3599_, 2);
                        v_idx_3600_ = leanh::lean_ctor_get(v___x_3535_, 1);
                        leanh::lean_inc(v_idx_3600_);
                        v_struct_3601_ = leanh::lean_ctor_get(v___x_3535_, 2);
                        leanh::lean_inc_ref(v_struct_3601_);
                        v___x_3602_ = lean_st_ref_get(v_a_3515_);
                        v_env_3608_ = leanh::lean_ctor_get(v___x_3602_, 0);
                        leanh::lean_inc_ref(v_env_3608_);
                        leanh::lean_dec(v___x_3602_);
                        v___x_3609_ = lean_is_class(v_env_3608_, v_typeName_3599_);
                        if v___x_3609_ == 0 {
                            v___y_3604_ = v_struct_3601_;
                            state = 15;
                            continue;
                        } else {
                            v___x_3610_ = l_Lean_Meta_DiscrTree_mkNoindexAnnotation(v_struct_3601_);
                            v___y_3604_ = v___x_3610_;
                            state = 15;
                            continue;
                        }
                    }
                    1 => {
                        leanh::lean_del_object(v___x_3526_);
                        v_fvarId_3611_ = leanh::lean_ctor_get(v___x_3535_, 0);
                        leanh::lean_inc(v_fvarId_3611_);
                        v___x_3612_ = l_Lean_Expr_getAppNumArgs(v_a_3524_);
                        leanh::lean_inc(v___x_3612_);
                        v___x_3613_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3613_, 0, v_fvarId_3611_);
                        leanh::lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                        v_k_3537_ = v___x_3613_;
                        v_nargs_3538_ = v___x_3612_;
                        v_todo_3539_ = v_todo_3509_;
                        v___y_3540_ = v_a_3512_;
                        v___y_3541_ = v_a_3513_;
                        v___y_3542_ = v_a_3514_;
                        v___y_3543_ = v_a_3515_;
                        state = 5;
                        continue;
                    }
                    2 => {
                        leanh::lean_del_object(v___x_3526_);
                        leanh::lean_dec(v_a_3524_);
                        v_mvarId_3614_ = leanh::lean_ctor_get(v___x_3535_, 0);
                        leanh::lean_inc(v_mvarId_3614_);
                        leanh::lean_dec_ref_known(v___x_3535_, 1);
                        v___x_3615_ =
                            l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpMVarId;
                        v___x_3616_ = l_Lean_instBEqMVarId_beq(v_mvarId_3614_, v___x_3615_);
                        if v___x_3616_ == 0 {
                            v___x_3617_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(
                                v_mvarId_3614_,
                                v_a_3512_,
                                v_a_3513_,
                                v_a_3514_,
                                v_a_3515_,
                            );
                            if leanh::lean_obj_tag(v___x_3617_) == 0 {
                                v_a_3618_ = leanh::lean_ctor_get(v___x_3617_, 0);
                                v_isSharedCheck_3633_ =
                                    (!leanh::lean_is_exclusive(v___x_3617_)) as u8;
                                if v_isSharedCheck_3633_ == 0 {
                                    v___x_3620_ = v___x_3617_;
                                    v_isShared_3621_ = v_isSharedCheck_3633_;
                                    state = 16;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3618_);
                                    leanh::lean_dec(v___x_3617_);
                                    v___x_3620_ = leanh::lean_box(0);
                                    v_isShared_3621_ = v_isSharedCheck_3633_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_todo_3509_);
                                v_a_3634_ = leanh::lean_ctor_get(v___x_3617_, 0);
                                v_isSharedCheck_3641_ =
                                    (!leanh::lean_is_exclusive(v___x_3617_)) as u8;
                                if v_isSharedCheck_3641_ == 0 {
                                    v___x_3636_ = v___x_3617_;
                                    v_isShared_3637_ = v_isSharedCheck_3641_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3634_);
                                    leanh::lean_dec(v___x_3617_);
                                    v___x_3636_ = leanh::lean_box(0);
                                    v_isShared_3637_ = v_isSharedCheck_3641_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_mvarId_3614_);
                            v___x_3642_ = leanh::lean_box(0);
                            v___x_3643_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3643_, 0, v___x_3642_);
                            leanh::lean_ctor_set(v___x_3643_, 1, v_todo_3509_);
                            v___x_3644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                            return v___x_3644_;
                        }
                    }
                    7 => {
                        leanh::lean_del_object(v___x_3526_);
                        leanh::lean_dec(v_a_3524_);
                        v_binderType_3645_ = leanh::lean_ctor_get(v___x_3535_, 1);
                        leanh::lean_inc_ref(v_binderType_3645_);
                        leanh::lean_dec_ref_known(v___x_3535_, 3);
                        v___x_3646_ = leanh::lean_box(5);
                        v___x_3647_ = lean_array_push(v_todo_3509_, v_binderType_3645_);
                        v___x_3648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3648_, 0, v___x_3646_);
                        leanh::lean_ctor_set(v___x_3648_, 1, v___x_3647_);
                        v___x_3649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3649_, 0, v___x_3648_);
                        return v___x_3649_;
                    }
                    _ => {
                        leanh::lean_dec_ref(v___x_3535_);
                        leanh::lean_del_object(v___x_3526_);
                        leanh::lean_dec(v_a_3524_);
                        v___x_3650_ = leanh::lean_box(1);
                        v___x_3651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3651_, 0, v___x_3650_);
                        leanh::lean_ctor_set(v___x_3651_, 1, v_todo_3509_);
                        v___x_3652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3652_, 0, v___x_3651_);
                        return v___x_3652_;
                    }
                }
            }
            3 => {
                v___x_3530_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3530_, 0, v_v_3529_);
                v___x_3531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3531_, 0, v___x_3530_);
                leanh::lean_ctor_set(v___x_3531_, 1, v_todo_3509_);
                if v_isShared_3527_ == 0 {
                    leanh::lean_ctor_set(v___x_3526_, 0, v___x_3531_);
                    v___x_3533_ = v___x_3526_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
                    v___x_3533_ = v_reuseFailAlloc_3534_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3533_;
            }
            5 => {
                leanh::lean_inc(v_nargs_3538_);
                v___x_3544_ = l_Lean_Meta_getFunInfoNArgs(
                    v___x_3535_,
                    v_nargs_3538_,
                    v___y_3540_,
                    v___y_3541_,
                    v___y_3542_,
                    v___y_3543_,
                );
                if leanh::lean_obj_tag(v___x_3544_) == 0 {
                    if v_noIndexAtArgs_3511_ == 0 {
                        v_a_3545_ = leanh::lean_ctor_get(v___x_3544_, 0);
                        leanh::lean_inc(v_a_3545_);
                        leanh::lean_dec_ref_known(v___x_3544_, 1);
                        v_paramInfo_3546_ = leanh::lean_ctor_get(v_a_3545_, 0);
                        leanh::lean_inc_ref(v_paramInfo_3546_);
                        leanh::lean_dec(v_a_3545_);
                        v___x_3547_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3548_ = lean_nat_sub(v_nargs_3538_, v___x_3547_);
                        leanh::lean_dec(v_nargs_3538_);
                        v___x_3549_ =
                            l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgsAux(
                                v_paramInfo_3546_,
                                v___x_3548_,
                                v_a_3524_,
                                v_todo_3539_,
                                v___y_3540_,
                                v___y_3541_,
                                v___y_3542_,
                                v___y_3543_,
                            );
                        leanh::lean_dec_ref(v_paramInfo_3546_);
                        if leanh::lean_obj_tag(v___x_3549_) == 0 {
                            v_a_3550_ = leanh::lean_ctor_get(v___x_3549_, 0);
                            leanh::lean_inc(v_a_3550_);
                            leanh::lean_dec_ref_known(v___x_3549_, 1);
                            v___y_3518_ = v_k_3537_;
                            v_todo_3519_ = v_a_3550_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_k_3537_);
                            v_a_3551_ = leanh::lean_ctor_get(v___x_3549_, 0);
                            v_isSharedCheck_3558_ =
                                (!leanh::lean_is_exclusive(v___x_3549_)) as u8;
                            if v_isSharedCheck_3558_ == 0 {
                                v___x_3553_ = v___x_3549_;
                                v_isShared_3554_ = v_isSharedCheck_3558_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3551_);
                                leanh::lean_dec(v___x_3549_);
                                v___x_3553_ = leanh::lean_box(0);
                                v_isShared_3554_ = v_isSharedCheck_3558_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_3544_, 1);
                        leanh::lean_dec(v_a_3524_);
                        v___x_3559_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushWildcards(v_nargs_3538_, v_todo_3539_);
                        v___y_3518_ = v_k_3537_;
                        v_todo_3519_ = v___x_3559_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_todo_3539_);
                    leanh::lean_dec(v_nargs_3538_);
                    leanh::lean_dec(v_k_3537_);
                    leanh::lean_dec(v_a_3524_);
                    v_a_3560_ = leanh::lean_ctor_get(v___x_3544_, 0);
                    v_isSharedCheck_3567_ = (!leanh::lean_is_exclusive(v___x_3544_)) as u8;
                    if v_isSharedCheck_3567_ == 0 {
                        v___x_3562_ = v___x_3544_;
                        v_isShared_3563_ = v_isSharedCheck_3567_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3560_);
                        leanh::lean_dec(v___x_3544_);
                        v___x_3562_ = leanh::lean_box(0);
                        v_isShared_3563_ = v_isSharedCheck_3567_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3554_ == 0 {
                    v___x_3556_ = v___x_3553_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3557_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
                    v___x_3556_ = v_reuseFailAlloc_3557_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3556_;
            }
            8 => {
                if v_isShared_3563_ == 0 {
                    v___x_3565_ = v___x_3562_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3566_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
                    v___x_3565_ = v_reuseFailAlloc_3566_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3565_;
            }
            10 => {
                v___x_3575_ = l_Lean_Expr_getAppNumArgs(v_a_3524_);
                leanh::lean_inc(v___x_3575_);
                v___x_3576_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3576_, 0, v_declName_3569_);
                leanh::lean_ctor_set(v___x_3576_, 1, v___x_3575_);
                v_k_3537_ = v___x_3576_;
                v_nargs_3538_ = v___x_3575_;
                v_todo_3539_ = v_todo_3509_;
                v___y_3540_ = v___y_3571_;
                v___y_3541_ = v___y_3572_;
                v___y_3542_ = v___y_3573_;
                v___y_3543_ = v___y_3574_;
                state = 5;
                continue;
            }
            11 => {
                v___x_3584_ = (leanh::lean_unbox(v_a_3580_) as u8);
                leanh::lean_dec(v_a_3580_);
                if v___x_3584_ == 0 {
                    leanh::lean_del_object(v___x_3582_);
                    v___y_3571_ = v_a_3512_;
                    v___y_3572_ = v_a_3513_;
                    v___y_3573_ = v_a_3514_;
                    v___y_3574_ = v_a_3515_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_3535_, 2);
                    leanh::lean_dec(v_declName_3569_);
                    leanh::lean_dec(v_a_3524_);
                    v___x_3585_ = leanh::lean_box(0);
                    v___x_3586_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3586_, 0, v___x_3585_);
                    leanh::lean_ctor_set(v___x_3586_, 1, v_todo_3509_);
                    if v_isShared_3583_ == 0 {
                        leanh::lean_ctor_set(v___x_3582_, 0, v___x_3586_);
                        v___x_3588_ = v___x_3582_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
                        v___x_3588_ = v_reuseFailAlloc_3589_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_3588_;
            }
            13 => {
                if v_isShared_3594_ == 0 {
                    v___x_3596_ = v___x_3593_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
                    v___x_3596_ = v_reuseFailAlloc_3597_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3596_;
            }
            15 => {
                v___x_3605_ = l_Lean_Expr_getAppNumArgs(v_a_3524_);
                leanh::lean_inc(v___x_3605_);
                v___x_3606_ = leanh::lean_alloc_ctor(6, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3606_, 0, v_typeName_3599_);
                leanh::lean_ctor_set(v___x_3606_, 1, v_idx_3600_);
                leanh::lean_ctor_set(v___x_3606_, 2, v___x_3605_);
                v___x_3607_ = lean_array_push(v_todo_3509_, v___y_3604_);
                v_k_3537_ = v___x_3606_;
                v_nargs_3538_ = v___x_3605_;
                v_todo_3539_ = v___x_3607_;
                v___y_3540_ = v_a_3512_;
                v___y_3541_ = v_a_3513_;
                v___y_3542_ = v_a_3514_;
                v___y_3543_ = v_a_3515_;
                state = 5;
                continue;
            }
            16 => {
                v___x_3622_ = (leanh::lean_unbox(v_a_3618_) as u8);
                leanh::lean_dec(v_a_3618_);
                if v___x_3622_ == 0 {
                    v___x_3623_ = leanh::lean_box(0);
                    v___x_3624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3624_, 0, v___x_3623_);
                    leanh::lean_ctor_set(v___x_3624_, 1, v_todo_3509_);
                    if v_isShared_3621_ == 0 {
                        leanh::lean_ctor_set(v___x_3620_, 0, v___x_3624_);
                        v___x_3626_ = v___x_3620_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3627_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
                        v___x_3626_ = v_reuseFailAlloc_3627_;
                        state = 17;
                        continue;
                    }
                } else {
                    v___x_3628_ = leanh::lean_box(1);
                    v___x_3629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3629_, 0, v___x_3628_);
                    leanh::lean_ctor_set(v___x_3629_, 1, v_todo_3509_);
                    if v_isShared_3621_ == 0 {
                        leanh::lean_ctor_set(v___x_3620_, 0, v___x_3629_);
                        v___x_3631_ = v___x_3620_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3632_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
                        v___x_3631_ = v_reuseFailAlloc_3632_;
                        state = 18;
                        continue;
                    }
                }
            }
            17 => {
                return v___x_3626_;
            }
            18 => {
                return v___x_3631_;
            }
            19 => {
                if v_isShared_3637_ == 0 {
                    v___x_3639_ = v___x_3636_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
                    v___x_3639_ = v_reuseFailAlloc_3640_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3639_;
            }
            21 => {
                if v_isShared_3657_ == 0 {
                    v___x_3659_ = v___x_3656_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs___boxed(
    mut v_root_3665_: *mut leanh::LeanObject,
    mut v_todo_3666_: *mut leanh::LeanObject,
    mut v_e_3667_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3668_: *mut leanh::LeanObject,
    mut v_a_3669_: *mut leanh::LeanObject,
    mut v_a_3670_: *mut leanh::LeanObject,
    mut v_a_3671_: *mut leanh::LeanObject,
    mut v_a_3672_: *mut leanh::LeanObject,
    mut v_a_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_boxed_3674_: u8 = 0;
    let mut v_noIndexAtArgs_boxed_3675_: u8 = 0;
    let mut v_res_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_boxed_3674_ = (leanh::lean_unbox(v_root_3665_) as u8);
    v_noIndexAtArgs_boxed_3675_ = (leanh::lean_unbox(v_noIndexAtArgs_3668_) as u8);
    v_res_3676_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(
        v_root_boxed_3674_,
        v_todo_3666_,
        v_e_3667_,
        v_noIndexAtArgs_boxed_3675_,
        v_a_3669_,
        v_a_3670_,
        v_a_3671_,
        v_a_3672_,
    );
    leanh::lean_dec(v_a_3672_);
    leanh::lean_dec_ref(v_a_3671_);
    leanh::lean_dec(v_a_3670_);
    leanh::lean_dec_ref(v_a_3669_);
    return v_res_3676_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mkPathAux(
    mut v_root_3677_: u8,
    mut v_todo_3678_: *mut leanh::LeanObject,
    mut v_keys_3679_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3680_: u8,
    mut v_a_3681_: *mut leanh::LeanObject,
    mut v_a_3682_: *mut leanh::LeanObject,
    mut v_a_3683_: *mut leanh::LeanObject,
    mut v_a_3684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3707_: u8 = 0;
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3686_ = lean_array_get_size(v_todo_3678_);
                v___x_3687_ = leanh::lean_unsigned_to_nat(0);
                v___x_3688_ = lean_nat_dec_eq(v___x_3686_, v___x_3687_);
                if v___x_3688_ == 0 {
                    v___x_3689_ = l_Lean_instInhabitedExpr;
                    v___x_3690_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3691_ = lean_nat_sub(v___x_3686_, v___x_3690_);
                    v_e_3692_ = lean_array_get(v___x_3689_, v_todo_3678_, v___x_3691_);
                    leanh::lean_dec(v___x_3691_);
                    v_todo_3693_ = lean_array_pop(v_todo_3678_);
                    v___x_3694_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_pushArgs(
                            v_root_3677_,
                            v_todo_3693_,
                            v_e_3692_,
                            v_noIndexAtArgs_3680_,
                            v_a_3681_,
                            v_a_3682_,
                            v_a_3683_,
                            v_a_3684_,
                        );
                    if leanh::lean_obj_tag(v___x_3694_) == 0 {
                        v_a_3695_ = leanh::lean_ctor_get(v___x_3694_, 0);
                        leanh::lean_inc(v_a_3695_);
                        leanh::lean_dec_ref_known(v___x_3694_, 1);
                        v_fst_3696_ = leanh::lean_ctor_get(v_a_3695_, 0);
                        leanh::lean_inc(v_fst_3696_);
                        v_snd_3697_ = leanh::lean_ctor_get(v_a_3695_, 1);
                        leanh::lean_inc(v_snd_3697_);
                        leanh::lean_dec(v_a_3695_);
                        v___x_3698_ = lean_array_push(v_keys_3679_, v_fst_3696_);
                        v_root_3677_ = v___x_3688_;
                        v_todo_3678_ = v_snd_3697_;
                        v_keys_3679_ = v___x_3698_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_keys_3679_);
                        v_a_3700_ = leanh::lean_ctor_get(v___x_3694_, 0);
                        v_isSharedCheck_3707_ =
                            (!leanh::lean_is_exclusive(v___x_3694_)) as u8;
                        if v_isSharedCheck_3707_ == 0 {
                            v___x_3702_ = v___x_3694_;
                            v_isShared_3703_ = v_isSharedCheck_3707_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3700_);
                            leanh::lean_dec(v___x_3694_);
                            v___x_3702_ = leanh::lean_box(0);
                            v_isShared_3703_ = v_isSharedCheck_3707_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_todo_3678_);
                    v___x_3708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3708_, 0, v_keys_3679_);
                    return v___x_3708_;
                }
            }
            1 => {
                if v_isShared_3703_ == 0 {
                    v___x_3705_ = v___x_3702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3706_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
                    v___x_3705_ = v_reuseFailAlloc_3706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_mkPathAux___boxed(
    mut v_root_3709_: *mut leanh::LeanObject,
    mut v_todo_3710_: *mut leanh::LeanObject,
    mut v_keys_3711_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3712_: *mut leanh::LeanObject,
    mut v_a_3713_: *mut leanh::LeanObject,
    mut v_a_3714_: *mut leanh::LeanObject,
    mut v_a_3715_: *mut leanh::LeanObject,
    mut v_a_3716_: *mut leanh::LeanObject,
    mut v_a_3717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_boxed_3718_: u8 = 0;
    let mut v_noIndexAtArgs_boxed_3719_: u8 = 0;
    let mut v_res_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_boxed_3718_ = (leanh::lean_unbox(v_root_3709_) as u8);
    v_noIndexAtArgs_boxed_3719_ = (leanh::lean_unbox(v_noIndexAtArgs_3712_) as u8);
    v_res_3720_ = l_Lean_Meta_DiscrTree_mkPathAux(
        v_root_boxed_3718_,
        v_todo_3710_,
        v_keys_3711_,
        v_noIndexAtArgs_boxed_3719_,
        v_a_3713_,
        v_a_3714_,
        v_a_3715_,
        v_a_3716_,
    );
    leanh::lean_dec(v_a_3716_);
    leanh::lean_dec_ref(v_a_3715_);
    leanh::lean_dec(v_a_3714_);
    leanh::lean_dec_ref(v_a_3713_);
    return v_res_3720_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity()
-> *mut leanh::LeanObject {
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = leanh::lean_unsigned_to_nat(8);
    return v___x_3721_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_mkPath___closed__0() -> u64 {
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: u64 = 0;
    v___x_3722_ = 2;
    v___x_3723_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3722_);
    return v___x_3723_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_mkPath(
    mut v_e_3724_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3725_: u8,
    mut v_a_3726_: *mut leanh::LeanObject,
    mut v_a_3727_: *mut leanh::LeanObject,
    mut v_a_3728_: *mut leanh::LeanObject,
    mut v_a_3729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3732_: u8 = 0;
    let mut v_ctxApprox_3733_: u8 = 0;
    let mut v_quasiPatternApprox_3734_: u8 = 0;
    let mut v_constApprox_3735_: u8 = 0;
    let mut v_isDefEqStuckEx_3736_: u8 = 0;
    let mut v_unificationHints_3737_: u8 = 0;
    let mut v_proofIrrelevance_3738_: u8 = 0;
    let mut v_assignSyntheticOpaque_3739_: u8 = 0;
    let mut v_offsetCnstrs_3740_: u8 = 0;
    let mut v_etaStruct_3741_: u8 = 0;
    let mut v_univApprox_3742_: u8 = 0;
    let mut v_iota_3743_: u8 = 0;
    let mut v_beta_3744_: u8 = 0;
    let mut v_proj_3745_: u8 = 0;
    let mut v_zeta_3746_: u8 = 0;
    let mut v_zetaDelta_3747_: u8 = 0;
    let mut v_zetaUnused_3748_: u8 = 0;
    let mut v_zetaHave_3749_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v_trackZetaDelta_3753_: u8 = 0;
    let mut v_zetaDeltaSet_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3760_: u8 = 0;
    let mut v_inTypeClassResolution_3761_: u8 = 0;
    let mut v_cacheInferType_3762_: u8 = 0;
    let mut v___x_3763_: u8 = 0;
    let mut v_config_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: u64 = 0;
    let mut v___x_3767_: u64 = 0;
    let mut v___x_3768_: u64 = 0;
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: u8 = 0;
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: u64 = 0;
    let mut v___x_3774_: u64 = 0;
    let mut v_key_3775_: u64 = 0;
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3731_ = l_Lean_Meta_Context_config(v_a_3726_);
                v_foApprox_3732_ = leanh::lean_ctor_get_uint8(v___x_3731_, 0 as u32);
                v_ctxApprox_3733_ = leanh::lean_ctor_get_uint8(v___x_3731_, 1 as u32);
                v_quasiPatternApprox_3734_ =
                    leanh::lean_ctor_get_uint8(v___x_3731_, 2 as u32);
                v_constApprox_3735_ = leanh::lean_ctor_get_uint8(v___x_3731_, 3 as u32);
                v_isDefEqStuckEx_3736_ = leanh::lean_ctor_get_uint8(v___x_3731_, 4 as u32);
                v_unificationHints_3737_ = leanh::lean_ctor_get_uint8(v___x_3731_, 5 as u32);
                v_proofIrrelevance_3738_ = leanh::lean_ctor_get_uint8(v___x_3731_, 6 as u32);
                v_assignSyntheticOpaque_3739_ =
                    leanh::lean_ctor_get_uint8(v___x_3731_, 7 as u32);
                v_offsetCnstrs_3740_ = leanh::lean_ctor_get_uint8(v___x_3731_, 8 as u32);
                v_etaStruct_3741_ = leanh::lean_ctor_get_uint8(v___x_3731_, 10 as u32);
                v_univApprox_3742_ = leanh::lean_ctor_get_uint8(v___x_3731_, 11 as u32);
                v_iota_3743_ = leanh::lean_ctor_get_uint8(v___x_3731_, 12 as u32);
                v_beta_3744_ = leanh::lean_ctor_get_uint8(v___x_3731_, 13 as u32);
                v_proj_3745_ = leanh::lean_ctor_get_uint8(v___x_3731_, 14 as u32);
                v_zeta_3746_ = leanh::lean_ctor_get_uint8(v___x_3731_, 15 as u32);
                v_zetaDelta_3747_ = leanh::lean_ctor_get_uint8(v___x_3731_, 16 as u32);
                v_zetaUnused_3748_ = leanh::lean_ctor_get_uint8(v___x_3731_, 17 as u32);
                v_zetaHave_3749_ = leanh::lean_ctor_get_uint8(v___x_3731_, 18 as u32);
                v_isSharedCheck_3780_ = (!leanh::lean_is_exclusive(v___x_3731_)) as u8;
                if v_isSharedCheck_3780_ == 0 {
                    v___x_3751_ = v___x_3731_;
                    v_isShared_3752_ = v_isSharedCheck_3780_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3731_);
                    v___x_3751_ = leanh::lean_box(0);
                    v_isShared_3752_ = v_isSharedCheck_3780_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_3753_ = leanh::lean_ctor_get_uint8(
                    v_a_3726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3754_ = leanh::lean_ctor_get(v_a_3726_, 1);
                v_lctx_3755_ = leanh::lean_ctor_get(v_a_3726_, 2);
                v_localInstances_3756_ = leanh::lean_ctor_get(v_a_3726_, 3);
                v_defEqCtx_x3f_3757_ = leanh::lean_ctor_get(v_a_3726_, 4);
                v_synthPendingDepth_3758_ = leanh::lean_ctor_get(v_a_3726_, 5);
                v_canUnfold_x3f_3759_ = leanh::lean_ctor_get(v_a_3726_, 6);
                v_univApprox_3760_ = leanh::lean_ctor_get_uint8(
                    v_a_3726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3761_ = leanh::lean_ctor_get_uint8(
                    v_a_3726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3762_ = leanh::lean_ctor_get_uint8(
                    v_a_3726_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3763_ = 2;
                if v_isShared_3752_ == 0 {
                    v_config_3765_ = v___x_3751_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3779_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        0 as u32,
                        v_foApprox_3732_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        1 as u32,
                        v_ctxApprox_3733_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        2 as u32,
                        v_quasiPatternApprox_3734_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        3 as u32,
                        v_constApprox_3735_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        4 as u32,
                        v_isDefEqStuckEx_3736_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        5 as u32,
                        v_unificationHints_3737_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        6 as u32,
                        v_proofIrrelevance_3738_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        7 as u32,
                        v_assignSyntheticOpaque_3739_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        8 as u32,
                        v_offsetCnstrs_3740_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        10 as u32,
                        v_etaStruct_3741_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        11 as u32,
                        v_univApprox_3742_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        12 as u32,
                        v_iota_3743_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        13 as u32,
                        v_beta_3744_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        14 as u32,
                        v_proj_3745_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        15 as u32,
                        v_zeta_3746_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        16 as u32,
                        v_zetaDelta_3747_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        17 as u32,
                        v_zetaUnused_3748_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        18 as u32,
                        v_zetaHave_3749_,
                    );
                    v_config_3765_ = v_reuseFailAlloc_3779_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_3765_, 9 as u32, v___x_3763_);
                v___x_3766_ = l_Lean_Meta_Context_configKey(v_a_3726_);
                v___x_3767_ = 3u64;
                v___x_3768_ = lean_uint64_shift_right(v___x_3766_, v___x_3767_);
                v___x_3769_ = leanh::lean_unsigned_to_nat(8);
                v_todo_3770_ = lean_mk_empty_array_with_capacity(v___x_3769_);
                v___x_3771_ = 1;
                leanh::lean_inc_ref(v_todo_3770_);
                v___x_3772_ = lean_array_push(v_todo_3770_, v_e_3724_);
                v___x_3773_ = lean_uint64_shift_left(v___x_3768_, v___x_3767_);
                v___x_3774_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0_once),
                    _init_l_Lean_Meta_DiscrTree_mkPath___closed__0,
                );
                v_key_3775_ = lean_uint64_lor(v___x_3773_, v___x_3774_);
                v___x_3776_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3776_, 0, v_config_3765_);
                leanh::lean_ctor_set_uint64(
                    v___x_3776_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_3775_,
                );
                leanh::lean_inc(v_canUnfold_x3f_3759_);
                leanh::lean_inc(v_synthPendingDepth_3758_);
                leanh::lean_inc(v_defEqCtx_x3f_3757_);
                leanh::lean_inc_ref(v_localInstances_3756_);
                leanh::lean_inc_ref(v_lctx_3755_);
                leanh::lean_inc(v_zetaDeltaSet_3754_);
                v___x_3777_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_3777_, 0, v___x_3776_);
                leanh::lean_ctor_set(v___x_3777_, 1, v_zetaDeltaSet_3754_);
                leanh::lean_ctor_set(v___x_3777_, 2, v_lctx_3755_);
                leanh::lean_ctor_set(v___x_3777_, 3, v_localInstances_3756_);
                leanh::lean_ctor_set(v___x_3777_, 4, v_defEqCtx_x3f_3757_);
                leanh::lean_ctor_set(v___x_3777_, 5, v_synthPendingDepth_3758_);
                leanh::lean_ctor_set(v___x_3777_, 6, v_canUnfold_x3f_3759_);
                leanh::lean_ctor_set_uint8(
                    v___x_3777_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3753_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3777_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3760_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3777_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3761_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3777_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3762_,
                );
                v___x_3778_ = l_Lean_Meta_DiscrTree_mkPathAux(
                    v___x_3771_,
                    v___x_3772_,
                    v_todo_3770_,
                    v_noIndexAtArgs_3725_,
                    v___x_3777_,
                    v_a_3727_,
                    v_a_3728_,
                    v_a_3729_,
                );
                leanh::lean_dec_ref_known(v___x_3777_, 7);
                return v___x_3778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_mkPath___boxed(
    mut v_e_3781_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3782_: *mut leanh::LeanObject,
    mut v_a_3783_: *mut leanh::LeanObject,
    mut v_a_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_noIndexAtArgs_boxed_3788_: u8 = 0;
    let mut v_res_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_noIndexAtArgs_boxed_3788_ = (leanh::lean_unbox(v_noIndexAtArgs_3782_) as u8);
    v_res_3789_ = l_Lean_Meta_DiscrTree_mkPath(
        v_e_3781_,
        v_noIndexAtArgs_boxed_3788_,
        v_a_3783_,
        v_a_3784_,
        v_a_3785_,
        v_a_3786_,
    );
    leanh::lean_dec(v_a_3786_);
    leanh::lean_dec_ref(v_a_3785_);
    leanh::lean_dec(v_a_3784_);
    leanh::lean_dec_ref(v_a_3783_);
    return v_res_3789_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insert___redArg(
    mut v_inst_3790_: *mut leanh::LeanObject,
    mut v_d_3791_: *mut leanh::LeanObject,
    mut v_e_3792_: *mut leanh::LeanObject,
    mut v_v_3793_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3794_: u8,
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
    mut v_a_3797_: *mut leanh::LeanObject,
    mut v_a_3798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v_a_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3813_: u8 = 0;
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3800_ = l_Lean_Meta_DiscrTree_mkPath(
                    v_e_3792_,
                    v_noIndexAtArgs_3794_,
                    v_a_3795_,
                    v_a_3796_,
                    v_a_3797_,
                    v_a_3798_,
                );
                if leanh::lean_obj_tag(v___x_3800_) == 0 {
                    v_a_3801_ = leanh::lean_ctor_get(v___x_3800_, 0);
                    v_isSharedCheck_3809_ = (!leanh::lean_is_exclusive(v___x_3800_)) as u8;
                    if v_isSharedCheck_3809_ == 0 {
                        v___x_3803_ = v___x_3800_;
                        v_isShared_3804_ = v_isSharedCheck_3809_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3801_);
                        leanh::lean_dec(v___x_3800_);
                        v___x_3803_ = leanh::lean_box(0);
                        v_isShared_3804_ = v_isSharedCheck_3809_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_v_3793_);
                    leanh::lean_dec_ref(v_d_3791_);
                    leanh::lean_dec_ref(v_inst_3790_);
                    v_a_3810_ = leanh::lean_ctor_get(v___x_3800_, 0);
                    v_isSharedCheck_3817_ = (!leanh::lean_is_exclusive(v___x_3800_)) as u8;
                    if v_isSharedCheck_3817_ == 0 {
                        v___x_3812_ = v___x_3800_;
                        v_isShared_3813_ = v_isSharedCheck_3817_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3810_);
                        leanh::lean_dec(v___x_3800_);
                        v___x_3812_ = leanh::lean_box(0);
                        v_isShared_3813_ = v_isSharedCheck_3817_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3805_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(
                    v_inst_3790_,
                    v_d_3791_,
                    v_a_3801_,
                    v_v_3793_,
                );
                if v_isShared_3804_ == 0 {
                    leanh::lean_ctor_set(v___x_3803_, 0, v___x_3805_);
                    v___x_3807_ = v___x_3803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
                    v___x_3807_ = v_reuseFailAlloc_3808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3807_;
            }
            3 => {
                if v_isShared_3813_ == 0 {
                    v___x_3815_ = v___x_3812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
                    v___x_3815_ = v_reuseFailAlloc_3816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insert___redArg___boxed(
    mut v_inst_3818_: *mut leanh::LeanObject,
    mut v_d_3819_: *mut leanh::LeanObject,
    mut v_e_3820_: *mut leanh::LeanObject,
    mut v_v_3821_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
    mut v_a_3824_: *mut leanh::LeanObject,
    mut v_a_3825_: *mut leanh::LeanObject,
    mut v_a_3826_: *mut leanh::LeanObject,
    mut v_a_3827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_noIndexAtArgs_boxed_3828_: u8 = 0;
    let mut v_res_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_noIndexAtArgs_boxed_3828_ = (leanh::lean_unbox(v_noIndexAtArgs_3822_) as u8);
    v_res_3829_ = l_Lean_Meta_DiscrTree_insert___redArg(
        v_inst_3818_,
        v_d_3819_,
        v_e_3820_,
        v_v_3821_,
        v_noIndexAtArgs_boxed_3828_,
        v_a_3823_,
        v_a_3824_,
        v_a_3825_,
        v_a_3826_,
    );
    leanh::lean_dec(v_a_3826_);
    leanh::lean_dec_ref(v_a_3825_);
    leanh::lean_dec(v_a_3824_);
    leanh::lean_dec_ref(v_a_3823_);
    return v_res_3829_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insert(
    mut v_00_u03b1_3830_: *mut leanh::LeanObject,
    mut v_inst_3831_: *mut leanh::LeanObject,
    mut v_d_3832_: *mut leanh::LeanObject,
    mut v_e_3833_: *mut leanh::LeanObject,
    mut v_v_3834_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3835_: u8,
    mut v_a_3836_: *mut leanh::LeanObject,
    mut v_a_3837_: *mut leanh::LeanObject,
    mut v_a_3838_: *mut leanh::LeanObject,
    mut v_a_3839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Lean_Meta_DiscrTree_insert___redArg(
        v_inst_3831_,
        v_d_3832_,
        v_e_3833_,
        v_v_3834_,
        v_noIndexAtArgs_3835_,
        v_a_3836_,
        v_a_3837_,
        v_a_3838_,
        v_a_3839_,
    );
    return v___x_3841_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insert___boxed(
    mut v_00_u03b1_3842_: *mut leanh::LeanObject,
    mut v_inst_3843_: *mut leanh::LeanObject,
    mut v_d_3844_: *mut leanh::LeanObject,
    mut v_e_3845_: *mut leanh::LeanObject,
    mut v_v_3846_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3847_: *mut leanh::LeanObject,
    mut v_a_3848_: *mut leanh::LeanObject,
    mut v_a_3849_: *mut leanh::LeanObject,
    mut v_a_3850_: *mut leanh::LeanObject,
    mut v_a_3851_: *mut leanh::LeanObject,
    mut v_a_3852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_noIndexAtArgs_boxed_3853_: u8 = 0;
    let mut v_res_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_noIndexAtArgs_boxed_3853_ = (leanh::lean_unbox(v_noIndexAtArgs_3847_) as u8);
    v_res_3854_ = l_Lean_Meta_DiscrTree_insert(
        v_00_u03b1_3842_,
        v_inst_3843_,
        v_d_3844_,
        v_e_3845_,
        v_v_3846_,
        v_noIndexAtArgs_boxed_3853_,
        v_a_3848_,
        v_a_3849_,
        v_a_3850_,
        v_a_3851_,
    );
    leanh::lean_dec(v_a_3851_);
    leanh::lean_dec_ref(v_a_3850_);
    leanh::lean_dec(v_a_3849_);
    leanh::lean_dec_ref(v_a_3848_);
    return v_res_3854_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3869_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3;
    v___x_3870_ = lean_array_get_size(v___x_3869_);
    return v___x_3870_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3876_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6;
    v___x_3877_ = lean_array_get_size(v___x_3876_);
    return v___x_3877_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(
    mut v_inst_3878_: *mut leanh::LeanObject,
    mut v_d_3879_: *mut leanh::LeanObject,
    mut v_e_3880_: *mut leanh::LeanObject,
    mut v_v_3881_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3882_: u8,
    mut v_a_3883_: *mut leanh::LeanObject,
    mut v_a_3884_: *mut leanh::LeanObject,
    mut v_a_3885_: *mut leanh::LeanObject,
    mut v_a_3886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: u8 = 0;
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: u8 = 0;
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut v_a_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3917_: u8 = 0;
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3888_ = l_Lean_Meta_DiscrTree_mkPath(
                    v_e_3880_,
                    v_noIndexAtArgs_3882_,
                    v_a_3883_,
                    v_a_3884_,
                    v_a_3885_,
                    v_a_3886_,
                );
                if leanh::lean_obj_tag(v___x_3888_) == 0 {
                    v_a_3889_ = leanh::lean_ctor_get(v___x_3888_, 0);
                    v_isSharedCheck_3913_ = (!leanh::lean_is_exclusive(v___x_3888_)) as u8;
                    if v_isSharedCheck_3913_ == 0 {
                        v___x_3891_ = v___x_3888_;
                        v_isShared_3892_ = v_isSharedCheck_3913_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3889_);
                        leanh::lean_dec(v___x_3888_);
                        v___x_3891_ = leanh::lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3913_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_v_3881_);
                    leanh::lean_dec_ref(v_d_3879_);
                    leanh::lean_dec_ref(v_inst_3878_);
                    v_a_3914_ = leanh::lean_ctor_get(v___x_3888_, 0);
                    v_isSharedCheck_3921_ = (!leanh::lean_is_exclusive(v___x_3888_)) as u8;
                    if v_isSharedCheck_3921_ == 0 {
                        v___x_3916_ = v___x_3888_;
                        v_isShared_3917_ = v_isSharedCheck_3921_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3914_);
                        leanh::lean_dec(v___x_3888_);
                        v___x_3916_ = leanh::lean_box(0);
                        v_isShared_3917_ = v_isSharedCheck_3921_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3906_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__6;
                v___x_3907_ = lean_array_get_size(v_a_3889_);
                v___x_3908_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7_once
                    ),
                    _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__7,
                );
                v___x_3909_ = lean_nat_dec_eq(v___x_3907_, v___x_3908_);
                if v___x_3909_ == 0 {
                    state = 4;
                    continue;
                } else {
                    v___x_3910_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5;
                    v___x_3911_ =
                        l_Array_isEqvAux___redArg(v_a_3889_, v___x_3906_, v___x_3910_, v___x_3907_);
                    if v___x_3911_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3891_);
                        leanh::lean_dec(v_a_3889_);
                        leanh::lean_dec(v_v_3881_);
                        leanh::lean_dec_ref(v_inst_3878_);
                        v___x_3912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3912_, 0, v_d_3879_);
                        return v___x_3912_;
                    }
                }
            }
            2 => {
                v___x_3894_ = l_Lean_Meta_DiscrTree_insertKeyValue___redArg(
                    v_inst_3878_,
                    v_d_3879_,
                    v_a_3889_,
                    v_v_3881_,
                );
                if v_isShared_3892_ == 0 {
                    leanh::lean_ctor_set(v___x_3891_, 0, v___x_3894_);
                    v___x_3896_ = v___x_3891_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
                    v___x_3896_ = v_reuseFailAlloc_3897_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3896_;
            }
            4 => {
                v___x_3899_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__3;
                v___x_3900_ = lean_array_get_size(v_a_3889_);
                v___x_3901_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4_once
                    ),
                    _init_l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__4,
                );
                v___x_3902_ = lean_nat_dec_eq(v___x_3900_, v___x_3901_);
                if v___x_3902_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_3903_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___closed__5;
                    v___x_3904_ =
                        l_Array_isEqvAux___redArg(v_a_3889_, v___x_3899_, v___x_3903_, v___x_3900_);
                    if v___x_3904_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_3891_);
                        leanh::lean_dec(v_a_3889_);
                        leanh::lean_dec(v_v_3881_);
                        leanh::lean_dec_ref(v_inst_3878_);
                        v___x_3905_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3905_, 0, v_d_3879_);
                        return v___x_3905_;
                    }
                }
            }
            5 => {
                if v_isShared_3917_ == 0 {
                    v___x_3919_ = v___x_3916_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3920_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
                    v___x_3919_ = v_reuseFailAlloc_3920_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertIfSpecific___redArg___boxed(
    mut v_inst_3922_: *mut leanh::LeanObject,
    mut v_d_3923_: *mut leanh::LeanObject,
    mut v_e_3924_: *mut leanh::LeanObject,
    mut v_v_3925_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3926_: *mut leanh::LeanObject,
    mut v_a_3927_: *mut leanh::LeanObject,
    mut v_a_3928_: *mut leanh::LeanObject,
    mut v_a_3929_: *mut leanh::LeanObject,
    mut v_a_3930_: *mut leanh::LeanObject,
    mut v_a_3931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_noIndexAtArgs_boxed_3932_: u8 = 0;
    let mut v_res_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_noIndexAtArgs_boxed_3932_ = (leanh::lean_unbox(v_noIndexAtArgs_3926_) as u8);
    v_res_3933_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(
        v_inst_3922_,
        v_d_3923_,
        v_e_3924_,
        v_v_3925_,
        v_noIndexAtArgs_boxed_3932_,
        v_a_3927_,
        v_a_3928_,
        v_a_3929_,
        v_a_3930_,
    );
    leanh::lean_dec(v_a_3930_);
    leanh::lean_dec_ref(v_a_3929_);
    leanh::lean_dec(v_a_3928_);
    leanh::lean_dec_ref(v_a_3927_);
    return v_res_3933_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertIfSpecific(
    mut v_00_u03b1_3934_: *mut leanh::LeanObject,
    mut v_inst_3935_: *mut leanh::LeanObject,
    mut v_d_3936_: *mut leanh::LeanObject,
    mut v_e_3937_: *mut leanh::LeanObject,
    mut v_v_3938_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3939_: u8,
    mut v_a_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
    mut v_a_3942_: *mut leanh::LeanObject,
    mut v_a_3943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_Meta_DiscrTree_insertIfSpecific___redArg(
        v_inst_3935_,
        v_d_3936_,
        v_e_3937_,
        v_v_3938_,
        v_noIndexAtArgs_3939_,
        v_a_3940_,
        v_a_3941_,
        v_a_3942_,
        v_a_3943_,
    );
    return v___x_3945_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertIfSpecific___boxed(
    mut v_00_u03b1_3946_: *mut leanh::LeanObject,
    mut v_inst_3947_: *mut leanh::LeanObject,
    mut v_d_3948_: *mut leanh::LeanObject,
    mut v_e_3949_: *mut leanh::LeanObject,
    mut v_v_3950_: *mut leanh::LeanObject,
    mut v_noIndexAtArgs_3951_: *mut leanh::LeanObject,
    mut v_a_3952_: *mut leanh::LeanObject,
    mut v_a_3953_: *mut leanh::LeanObject,
    mut v_a_3954_: *mut leanh::LeanObject,
    mut v_a_3955_: *mut leanh::LeanObject,
    mut v_a_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_noIndexAtArgs_boxed_3957_: u8 = 0;
    let mut v_res_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_noIndexAtArgs_boxed_3957_ = (leanh::lean_unbox(v_noIndexAtArgs_3951_) as u8);
    v_res_3958_ = l_Lean_Meta_DiscrTree_insertIfSpecific(
        v_00_u03b1_3946_,
        v_inst_3947_,
        v_d_3948_,
        v_e_3949_,
        v_v_3950_,
        v_noIndexAtArgs_boxed_3957_,
        v_a_3952_,
        v_a_3953_,
        v_a_3954_,
        v_a_3955_,
    );
    leanh::lean_dec(v_a_3955_);
    leanh::lean_dec_ref(v_a_3954_);
    leanh::lean_dec(v_a_3953_);
    leanh::lean_dec_ref(v_a_3952_);
    return v_res_3958_;
}
pub unsafe fn l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(
    mut v_declName_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3962_ = lean_st_ref_get(v___y_3960_);
    v_env_3963_ = leanh::lean_ctor_get(v___x_3962_, 0);
    leanh::lean_inc_ref(v_env_3963_);
    leanh::lean_dec(v___x_3962_);
    v___x_3964_ = l_Lean_isRecCore(v_env_3963_, v_declName_3959_);
    v___x_3965_ = leanh::lean_box((v___x_3964_) as usize);
    v___x_3966_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3966_, 0, v___x_3965_);
    return v___x_3966_;
}
pub unsafe fn l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg___boxed(
    mut v_declName_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_3967_, v___y_3968_);
    leanh::lean_dec(v___y_3968_);
    return v_res_3970_;
}
pub unsafe fn l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(
    mut v_declName_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
    mut v___y_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3977_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_3971_, v___y_3975_);
    return v___x_3977_;
}
pub unsafe fn l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___boxed(
    mut v_declName_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3984_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2(v_declName_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
    leanh::lean_dec(v___y_3982_);
    leanh::lean_dec_ref(v___y_3981_);
    leanh::lean_dec(v___y_3980_);
    leanh::lean_dec_ref(v___y_3979_);
    return v_res_3984_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(
    mut v_a_3985_: *mut leanh::LeanObject,
    mut v_b_3986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3993_: u8 = 0;
    let mut v___x_3994_: u8 = 0;
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: u8 = 0;
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3988_ = leanh::lean_ctor_get(v_a_3985_, 0);
                v_start_3989_ = leanh::lean_ctor_get(v_a_3985_, 1);
                v_stop_3990_ = leanh::lean_ctor_get(v_a_3985_, 2);
                v_isSharedCheck_4007_ = (!leanh::lean_is_exclusive(v_a_3985_)) as u8;
                if v_isSharedCheck_4007_ == 0 {
                    v___x_3992_ = v_a_3985_;
                    v_isShared_3993_ = v_isSharedCheck_4007_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3990_);
                    leanh::lean_inc(v_start_3989_);
                    leanh::lean_inc(v_array_3988_);
                    leanh::lean_dec(v_a_3985_);
                    v___x_3992_ = leanh::lean_box(0);
                    v_isShared_3993_ = v_isSharedCheck_4007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3994_ = lean_nat_dec_lt(v_start_3989_, v_stop_3990_);
                if v___x_3994_ == 0 {
                    leanh::lean_del_object(v___x_3992_);
                    leanh::lean_dec(v_stop_3990_);
                    leanh::lean_dec(v_start_3989_);
                    leanh::lean_dec_ref(v_array_3988_);
                    v___x_3995_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3995_, 0, v_b_3986_);
                    return v___x_3995_;
                } else {
                    v___x_3996_ = leanh::lean_box(0);
                    v___x_3997_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3998_ = lean_nat_add(v_start_3989_, v___x_3997_);
                    leanh::lean_inc_ref(v_array_3988_);
                    if v_isShared_3993_ == 0 {
                        leanh::lean_ctor_set(v___x_3992_, 1, v___x_3998_);
                        v___x_4000_ = v___x_3992_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4006_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_array_3988_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 1, v___x_3998_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 2, v_stop_3990_);
                        v___x_4000_ = v_reuseFailAlloc_4006_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4001_ = lean_array_fget(v_array_3988_, v_start_3989_);
                leanh::lean_dec(v_start_3989_);
                leanh::lean_dec_ref(v_array_3988_);
                v___x_4002_ = l_Lean_Expr_hasExprMVar(v___x_4001_);
                leanh::lean_dec(v___x_4001_);
                if v___x_4002_ == 0 {
                    v_a_3985_ = v___x_4000_;
                    v_b_3986_ = v___x_3996_;
                    state = 0;
                    continue;
                } else {
                    v___x_4004_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
                    if leanh::lean_obj_tag(v___x_4004_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4004_, 1);
                        v_a_3985_ = v___x_4000_;
                        v_b_3986_ = v___x_3996_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_4000_);
                        return v___x_4004_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg___boxed(
    mut v_a_4008_: *mut leanh::LeanObject,
    mut v_b_4009_: *mut leanh::LeanObject,
    mut v___y_4010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_4008_, v_b_4009_);
    return v_res_4011_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(
    mut v_declName_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4015_ = lean_st_ref_get(v___y_4013_);
    v_env_4016_ = leanh::lean_ctor_get(v___x_4015_, 0);
    leanh::lean_inc_ref(v_env_4016_);
    leanh::lean_dec(v___x_4015_);
    v___x_4017_ = lean_get_reducibility_status(v_env_4016_, v_declName_4012_);
    v___x_4018_ = leanh::lean_box((v___x_4017_) as usize);
    v___x_4019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4019_, 0, v___x_4018_);
    return v___x_4019_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg___boxed(
    mut v_declName_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4023_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_4020_, v___y_4021_);
    leanh::lean_dec(v___y_4021_);
    return v_res_4023_;
}
pub unsafe fn l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(
    mut v_declName_4024_: *mut leanh::LeanObject,
    mut v___y_4025_: *mut leanh::LeanObject,
    mut v___y_4026_: *mut leanh::LeanObject,
    mut v___y_4027_: *mut leanh::LeanObject,
    mut v___y_4028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4034_: u8 = 0;
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: u8 = 0;
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4030_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_4024_, v___y_4028_);
                v_a_4031_ = leanh::lean_ctor_get(v___x_4030_, 0);
                v_isSharedCheck_4046_ = (!leanh::lean_is_exclusive(v___x_4030_)) as u8;
                if v_isSharedCheck_4046_ == 0 {
                    v___x_4033_ = v___x_4030_;
                    v_isShared_4034_ = v_isSharedCheck_4046_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4031_);
                    leanh::lean_dec(v___x_4030_);
                    v___x_4033_ = leanh::lean_box(0);
                    v_isShared_4034_ = v_isSharedCheck_4046_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4035_ = (leanh::lean_unbox(v_a_4031_) as u8);
                leanh::lean_dec(v_a_4031_);
                if v___x_4035_ == 0 {
                    v___x_4036_ = 1;
                    v___x_4037_ = leanh::lean_box((v___x_4036_) as usize);
                    if v_isShared_4034_ == 0 {
                        leanh::lean_ctor_set(v___x_4033_, 0, v___x_4037_);
                        v___x_4039_ = v___x_4033_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4040_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
                        v___x_4039_ = v_reuseFailAlloc_4040_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4041_ = 0;
                    v___x_4042_ = leanh::lean_box((v___x_4041_) as usize);
                    if v_isShared_4034_ == 0 {
                        leanh::lean_ctor_set(v___x_4033_, 0, v___x_4042_);
                        v___x_4044_ = v___x_4033_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4045_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
                        v___x_4044_ = v_reuseFailAlloc_4045_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4039_;
            }
            3 => {
                return v___x_4044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0___boxed(
    mut v_declName_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4053_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
    leanh::lean_dec(v___y_4051_);
    leanh::lean_dec_ref(v___y_4050_);
    leanh::lean_dec(v___y_4049_);
    leanh::lean_dec_ref(v___y_4048_);
    return v_res_4053_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = leanh::lean_box(0);
    v_dummy_4057_ = l_Lean_Expr_sort___override(v___x_4056_);
    return v_dummy_4057_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(
    mut v_e_4064_: *mut leanh::LeanObject,
    mut v_isMatch_4065_: u8,
    mut v_root_4066_: u8,
    mut v_a_4067_: *mut leanh::LeanObject,
    mut v_a_4068_: *mut leanh::LeanObject,
    mut v_a_4069_: *mut leanh::LeanObject,
    mut v_a_4070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4076_: u8 = 0;
    let mut v___y_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDefEqStuckEx_4100_: u8 = 0;
    let mut v___x_4101_: u8 = 0;
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4124_: u8 = 0;
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: u8 = 0;
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v_a_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut v_fvarId_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDefEqStuckEx_4167_: u8 = 0;
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4172_: u8 = 0;
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v_a_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4186_: u8 = 0;
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4190_: u8 = 0;
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4221_: u8 = 0;
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_a_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4072_ = l_Lean_Meta_DiscrTree_reduceDT(
                    v_e_4064_,
                    v_root_4066_,
                    v_a_4067_,
                    v_a_4068_,
                    v_a_4069_,
                    v_a_4070_,
                );
                if leanh::lean_obj_tag(v___x_4072_) == 0 {
                    v_a_4073_ = leanh::lean_ctor_get(v___x_4072_, 0);
                    v_isSharedCheck_4229_ = (!leanh::lean_is_exclusive(v___x_4072_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v___x_4075_ = v___x_4072_;
                        v_isShared_4076_ = v_isSharedCheck_4229_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4073_);
                        leanh::lean_dec(v___x_4072_);
                        v___x_4075_ = leanh::lean_box(0);
                        v_isShared_4076_ = v_isSharedCheck_4229_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4230_ = leanh::lean_ctor_get(v___x_4072_, 0);
                    v_isSharedCheck_4237_ = (!leanh::lean_is_exclusive(v___x_4072_)) as u8;
                    if v_isSharedCheck_4237_ == 0 {
                        v___x_4232_ = v___x_4072_;
                        v_isShared_4233_ = v_isSharedCheck_4237_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4230_);
                        leanh::lean_dec(v___x_4072_);
                        v___x_4232_ = leanh::lean_box(0);
                        v_isShared_4233_ = v_isSharedCheck_4237_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                if v_root_4066_ == 0 {
                    leanh::lean_inc(v_a_4073_);
                    v___x_4217_ =
                        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_toNatLit_x3f(
                            v_a_4073_,
                        );
                    if leanh::lean_obj_tag(v___x_4217_) == 1 {
                        leanh::lean_del_object(v___x_4075_);
                        leanh::lean_dec(v_a_4073_);
                        v_val_4218_ = leanh::lean_ctor_get(v___x_4217_, 0);
                        v_isSharedCheck_4228_ =
                            (!leanh::lean_is_exclusive(v___x_4217_)) as u8;
                        if v_isSharedCheck_4228_ == 0 {
                            v___x_4220_ = v___x_4217_;
                            v_isShared_4221_ = v_isSharedCheck_4228_;
                            state = 18;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4218_);
                            leanh::lean_dec(v___x_4217_);
                            v___x_4220_ = leanh::lean_box(0);
                            v_isShared_4221_ = v_isSharedCheck_4228_;
                            state = 18;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4217_);
                        v___y_4088_ = v_a_4067_;
                        v___y_4089_ = v_a_4068_;
                        v___y_4090_ = v_a_4069_;
                        v___y_4091_ = v_a_4070_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___y_4088_ = v_a_4067_;
                    v___y_4089_ = v_a_4068_;
                    v___y_4090_ = v_a_4069_;
                    v___y_4091_ = v_a_4070_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_4079_ = l_Lean_Expr_getAppNumArgs(v_a_4073_);
                leanh::lean_inc(v___x_4079_);
                v___x_4080_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4080_, 0, v___y_4078_);
                leanh::lean_ctor_set(v___x_4080_, 1, v___x_4079_);
                v___x_4081_ = lean_mk_empty_array_with_capacity(v___x_4079_);
                leanh::lean_dec(v___x_4079_);
                v___x_4082_ =
                    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_a_4073_, v___x_4081_);
                v___x_4083_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4083_, 0, v___x_4080_);
                leanh::lean_ctor_set(v___x_4083_, 1, v___x_4082_);
                if v_isShared_4076_ == 0 {
                    leanh::lean_ctor_set(v___x_4075_, 0, v___x_4083_);
                    v___x_4085_ = v___x_4075_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4086_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4083_);
                    v___x_4085_ = v_reuseFailAlloc_4086_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4085_;
            }
            4 => {
                v___x_4092_ = l_Lean_Expr_getAppFn(v_a_4073_);
                match leanh::lean_obj_tag(v___x_4092_) {
                    9 => {
                        leanh::lean_del_object(v___x_4075_);
                        leanh::lean_dec(v_a_4073_);
                        v_a_4093_ = leanh::lean_ctor_get(v___x_4092_, 0);
                        leanh::lean_inc_ref(v_a_4093_);
                        leanh::lean_dec_ref_known(v___x_4092_, 1);
                        v___x_4094_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4094_, 0, v_a_4093_);
                        v___x_4095_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0;
                        v___x_4096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4096_, 0, v___x_4094_);
                        leanh::lean_ctor_set(v___x_4096_, 1, v___x_4095_);
                        v___x_4097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4097_, 0, v___x_4096_);
                        return v___x_4097_;
                    }
                    4 => {
                        v_declName_4098_ = leanh::lean_ctor_get(v___x_4092_, 0);
                        leanh::lean_inc(v_declName_4098_);
                        leanh::lean_dec_ref_known(v___x_4092_, 2);
                        v___x_4099_ = l_Lean_Meta_Context_config(v___y_4088_);
                        v_isDefEqStuckEx_4100_ =
                            leanh::lean_ctor_get_uint8(v___x_4099_, 4 as u32);
                        leanh::lean_dec_ref(v___x_4099_);
                        if v_isDefEqStuckEx_4100_ == 0 {
                            v___y_4078_ = v_declName_4098_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4101_ = l_Lean_Expr_hasExprMVar(v_a_4073_);
                            if v___x_4101_ == 0 {
                                v___y_4078_ = v_declName_4098_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_declName_4098_);
                                v___x_4102_ = l_Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0(v_declName_4098_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
                                if leanh::lean_obj_tag(v___x_4102_) == 0 {
                                    v_a_4103_ = leanh::lean_ctor_get(v___x_4102_, 0);
                                    leanh::lean_inc(v_a_4103_);
                                    leanh::lean_dec_ref_known(v___x_4102_, 1);
                                    v___x_4104_ = (leanh::lean_unbox(v_a_4103_) as u8);
                                    leanh::lean_dec(v_a_4103_);
                                    if v___x_4104_ == 0 {
                                        v___x_4105_ = lean_st_ref_get(v___y_4091_);
                                        v_env_4106_ = leanh::lean_ctor_get(v___x_4105_, 0);
                                        leanh::lean_inc_ref(v_env_4106_);
                                        leanh::lean_dec(v___x_4105_);
                                        v___x_4107_ = l_Lean_Meta_isMatcherAppCore_x3f(
                                            v_env_4106_,
                                            v_a_4073_,
                                        );
                                        if leanh::lean_obj_tag(v___x_4107_) == 1 {
                                            v_val_4108_ =
                                                leanh::lean_ctor_get(v___x_4107_, 0);
                                            leanh::lean_inc(v_val_4108_);
                                            leanh::lean_dec_ref_known(v___x_4107_, 1);
                                            v_numDiscrs_4109_ =
                                                leanh::lean_ctor_get(v_val_4108_, 1);
                                            leanh::lean_inc(v_numDiscrs_4109_);
                                            v_nargs_4110_ = l_Lean_Expr_getAppNumArgs(v_a_4073_);
                                            v_dummy_4111_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1_once), _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__1);
                                            leanh::lean_inc(v_nargs_4110_);
                                            v___x_4112_ =
                                                lean_mk_array(v_nargs_4110_, v_dummy_4111_);
                                            v___x_4113_ = leanh::lean_unsigned_to_nat(1);
                                            v___x_4114_ = lean_nat_sub(v_nargs_4110_, v___x_4113_);
                                            leanh::lean_dec(v_nargs_4110_);
                                            leanh::lean_inc(v_a_4073_);
                                            v___x_4115_ =
                                                l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                                    v_a_4073_,
                                                    v___x_4112_,
                                                    v___x_4114_,
                                                );
                                            v___x_4116_ =
                                                l_Lean_Meta_Match_MatcherInfo_getFirstDiscrPos(
                                                    v_val_4108_,
                                                );
                                            leanh::lean_dec(v_val_4108_);
                                            v___x_4117_ =
                                                lean_nat_add(v___x_4116_, v_numDiscrs_4109_);
                                            leanh::lean_dec(v_numDiscrs_4109_);
                                            v___x_4118_ = l_Array_toSubarray___redArg(
                                                v___x_4115_,
                                                v___x_4116_,
                                                v___x_4117_,
                                            );
                                            v___x_4119_ = leanh::lean_box(0);
                                            v___x_4120_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v___x_4118_, v___x_4119_);
                                            if leanh::lean_obj_tag(v___x_4120_) == 0 {
                                                leanh::lean_dec_ref_known(v___x_4120_, 1);
                                                v___y_4078_ = v_declName_4098_;
                                                state = 2;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_declName_4098_);
                                                leanh::lean_del_object(v___x_4075_);
                                                leanh::lean_dec(v_a_4073_);
                                                v_a_4121_ =
                                                    leanh::lean_ctor_get(v___x_4120_, 0);
                                                v_isSharedCheck_4128_ =
                                                    (!leanh::lean_is_exclusive(v___x_4120_))
                                                        as u8;
                                                if v_isSharedCheck_4128_ == 0 {
                                                    v___x_4123_ = v___x_4120_;
                                                    v_isShared_4124_ = v_isSharedCheck_4128_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4121_);
                                                    leanh::lean_dec(v___x_4120_);
                                                    v___x_4123_ = leanh::lean_box(0);
                                                    v_isShared_4124_ = v_isSharedCheck_4128_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v___x_4107_);
                                            leanh::lean_inc(v_declName_4098_);
                                            v___x_4129_ = l_Lean_isRec___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__2___redArg(v_declName_4098_, v___y_4091_);
                                            v_a_4130_ = leanh::lean_ctor_get(v___x_4129_, 0);
                                            leanh::lean_inc(v_a_4130_);
                                            leanh::lean_dec_ref(v___x_4129_);
                                            v___x_4131_ =
                                                (leanh::lean_unbox(v_a_4130_) as u8);
                                            leanh::lean_dec(v_a_4130_);
                                            if v___x_4131_ == 0 {
                                                v___y_4078_ = v_declName_4098_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_4132_ =
                                                    l_Lean_Meta_throwIsDefEqStuck___redArg();
                                                if leanh::lean_obj_tag(v___x_4132_) == 0 {
                                                    leanh::lean_dec_ref_known(
                                                        v___x_4132_,
                                                        1,
                                                    );
                                                    v___y_4078_ = v_declName_4098_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v_declName_4098_);
                                                    leanh::lean_del_object(v___x_4075_);
                                                    leanh::lean_dec(v_a_4073_);
                                                    v_a_4133_ =
                                                        leanh::lean_ctor_get(v___x_4132_, 0);
                                                    v_isSharedCheck_4140_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4132_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4140_ == 0 {
                                                        v___x_4135_ = v___x_4132_;
                                                        v_isShared_4136_ = v_isSharedCheck_4140_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4133_);
                                                        leanh::lean_dec(v___x_4132_);
                                                        v___x_4135_ = leanh::lean_box(0);
                                                        v_isShared_4136_ = v_isSharedCheck_4140_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_4141_ = l_Lean_Meta_throwIsDefEqStuck___redArg();
                                        if leanh::lean_obj_tag(v___x_4141_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_4141_, 1);
                                            v___y_4078_ = v_declName_4098_;
                                            state = 2;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v_declName_4098_);
                                            leanh::lean_del_object(v___x_4075_);
                                            leanh::lean_dec(v_a_4073_);
                                            v_a_4142_ = leanh::lean_ctor_get(v___x_4141_, 0);
                                            v_isSharedCheck_4149_ =
                                                (!leanh::lean_is_exclusive(v___x_4141_))
                                                    as u8;
                                            if v_isSharedCheck_4149_ == 0 {
                                                v___x_4144_ = v___x_4141_;
                                                v_isShared_4145_ = v_isSharedCheck_4149_;
                                                state = 9;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4142_);
                                                leanh::lean_dec(v___x_4141_);
                                                v___x_4144_ = leanh::lean_box(0);
                                                v_isShared_4145_ = v_isSharedCheck_4149_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_declName_4098_);
                                    leanh::lean_del_object(v___x_4075_);
                                    leanh::lean_dec(v_a_4073_);
                                    v_a_4150_ = leanh::lean_ctor_get(v___x_4102_, 0);
                                    v_isSharedCheck_4157_ =
                                        (!leanh::lean_is_exclusive(v___x_4102_)) as u8;
                                    if v_isSharedCheck_4157_ == 0 {
                                        v___x_4152_ = v___x_4102_;
                                        v_isShared_4153_ = v_isSharedCheck_4157_;
                                        state = 11;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4150_);
                                        leanh::lean_dec(v___x_4102_);
                                        v___x_4152_ = leanh::lean_box(0);
                                        v_isShared_4153_ = v_isSharedCheck_4157_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_del_object(v___x_4075_);
                        v_fvarId_4158_ = leanh::lean_ctor_get(v___x_4092_, 0);
                        leanh::lean_inc(v_fvarId_4158_);
                        leanh::lean_dec_ref_known(v___x_4092_, 1);
                        v___x_4159_ = l_Lean_Expr_getAppNumArgs(v_a_4073_);
                        leanh::lean_inc(v___x_4159_);
                        v___x_4160_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4160_, 0, v_fvarId_4158_);
                        leanh::lean_ctor_set(v___x_4160_, 1, v___x_4159_);
                        v___x_4161_ = lean_mk_empty_array_with_capacity(v___x_4159_);
                        leanh::lean_dec(v___x_4159_);
                        v___x_4162_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(
                            v_a_4073_,
                            v___x_4161_,
                        );
                        v___x_4163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4163_, 0, v___x_4160_);
                        leanh::lean_ctor_set(v___x_4163_, 1, v___x_4162_);
                        v___x_4164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4164_, 0, v___x_4163_);
                        return v___x_4164_;
                    }
                    2 => {
                        leanh::lean_del_object(v___x_4075_);
                        leanh::lean_dec(v_a_4073_);
                        if v_isMatch_4065_ == 0 {
                            v_mvarId_4165_ = leanh::lean_ctor_get(v___x_4092_, 0);
                            leanh::lean_inc(v_mvarId_4165_);
                            leanh::lean_dec_ref_known(v___x_4092_, 1);
                            v___x_4166_ = l_Lean_Meta_Context_config(v___y_4088_);
                            v_isDefEqStuckEx_4167_ =
                                leanh::lean_ctor_get_uint8(v___x_4166_, 4 as u32);
                            leanh::lean_dec_ref(v___x_4166_);
                            if v_isDefEqStuckEx_4167_ == 0 {
                                v___x_4168_ = l_Lean_MVarId_isReadOnlyOrSyntheticOpaque(
                                    v_mvarId_4165_,
                                    v___y_4088_,
                                    v___y_4089_,
                                    v___y_4090_,
                                    v___y_4091_,
                                );
                                if leanh::lean_obj_tag(v___x_4168_) == 0 {
                                    v_a_4169_ = leanh::lean_ctor_get(v___x_4168_, 0);
                                    v_isSharedCheck_4182_ =
                                        (!leanh::lean_is_exclusive(v___x_4168_)) as u8;
                                    if v_isSharedCheck_4182_ == 0 {
                                        v___x_4171_ = v___x_4168_;
                                        v_isShared_4172_ = v_isSharedCheck_4182_;
                                        state = 13;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4169_);
                                        leanh::lean_dec(v___x_4168_);
                                        v___x_4171_ = leanh::lean_box(0);
                                        v_isShared_4172_ = v_isSharedCheck_4182_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    v_a_4183_ = leanh::lean_ctor_get(v___x_4168_, 0);
                                    v_isSharedCheck_4190_ =
                                        (!leanh::lean_is_exclusive(v___x_4168_)) as u8;
                                    if v_isSharedCheck_4190_ == 0 {
                                        v___x_4185_ = v___x_4168_;
                                        v_isShared_4186_ = v_isSharedCheck_4190_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4183_);
                                        leanh::lean_dec(v___x_4168_);
                                        v___x_4185_ = leanh::lean_box(0);
                                        v_isShared_4186_ = v_isSharedCheck_4190_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_mvarId_4165_);
                                v___x_4191_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
                                v___x_4192_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4192_, 0, v___x_4191_);
                                return v___x_4192_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_4092_, 1);
                            v___x_4193_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
                            v___x_4194_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4194_, 0, v___x_4193_);
                            return v___x_4194_;
                        }
                    }
                    11 => {
                        leanh::lean_del_object(v___x_4075_);
                        v_typeName_4195_ = leanh::lean_ctor_get(v___x_4092_, 0);
                        leanh::lean_inc(v_typeName_4195_);
                        v_idx_4196_ = leanh::lean_ctor_get(v___x_4092_, 1);
                        leanh::lean_inc(v_idx_4196_);
                        v_struct_4197_ = leanh::lean_ctor_get(v___x_4092_, 2);
                        leanh::lean_inc_ref(v_struct_4197_);
                        leanh::lean_dec_ref_known(v___x_4092_, 3);
                        v___x_4198_ = l_Lean_Expr_getAppNumArgs(v_a_4073_);
                        leanh::lean_inc(v___x_4198_);
                        v___x_4199_ = leanh::lean_alloc_ctor(6, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_4199_, 0, v_typeName_4195_);
                        leanh::lean_ctor_set(v___x_4199_, 1, v_idx_4196_);
                        leanh::lean_ctor_set(v___x_4199_, 2, v___x_4198_);
                        v___x_4200_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4201_ = lean_mk_empty_array_with_capacity(v___x_4200_);
                        v___x_4202_ = lean_array_push(v___x_4201_, v_struct_4197_);
                        v___x_4203_ = lean_mk_empty_array_with_capacity(v___x_4198_);
                        leanh::lean_dec(v___x_4198_);
                        v___x_4204_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(
                            v_a_4073_,
                            v___x_4203_,
                        );
                        v___x_4205_ = l_Array_append___redArg(v___x_4202_, v___x_4204_);
                        leanh::lean_dec_ref(v___x_4204_);
                        v___x_4206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4206_, 0, v___x_4199_);
                        leanh::lean_ctor_set(v___x_4206_, 1, v___x_4205_);
                        v___x_4207_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4207_, 0, v___x_4206_);
                        return v___x_4207_;
                    }
                    7 => {
                        leanh::lean_del_object(v___x_4075_);
                        leanh::lean_dec(v_a_4073_);
                        v_binderType_4208_ = leanh::lean_ctor_get(v___x_4092_, 1);
                        leanh::lean_inc_ref(v_binderType_4208_);
                        leanh::lean_dec_ref_known(v___x_4092_, 3);
                        v___x_4209_ = leanh::lean_box(5);
                        v___x_4210_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4211_ = lean_mk_empty_array_with_capacity(v___x_4210_);
                        v___x_4212_ = lean_array_push(v___x_4211_, v_binderType_4208_);
                        v___x_4213_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4213_, 0, v___x_4209_);
                        leanh::lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                        v___x_4214_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4214_, 0, v___x_4213_);
                        return v___x_4214_;
                    }
                    _ => {
                        leanh::lean_dec_ref(v___x_4092_);
                        leanh::lean_del_object(v___x_4075_);
                        leanh::lean_dec(v_a_4073_);
                        v___x_4215_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
                        v___x_4216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4216_, 0, v___x_4215_);
                        return v___x_4216_;
                    }
                }
            }
            5 => {
                if v_isShared_4124_ == 0 {
                    v___x_4126_ = v___x_4123_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4121_);
                    v___x_4126_ = v_reuseFailAlloc_4127_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4126_;
            }
            7 => {
                if v_isShared_4136_ == 0 {
                    v___x_4138_ = v___x_4135_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4138_;
            }
            9 => {
                if v_isShared_4145_ == 0 {
                    v___x_4147_ = v___x_4144_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
                    v___x_4147_ = v_reuseFailAlloc_4148_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4147_;
            }
            11 => {
                if v_isShared_4153_ == 0 {
                    v___x_4155_ = v___x_4152_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
                    v___x_4155_ = v_reuseFailAlloc_4156_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4155_;
            }
            13 => {
                v___x_4173_ = (leanh::lean_unbox(v_a_4169_) as u8);
                leanh::lean_dec(v_a_4169_);
                if v___x_4173_ == 0 {
                    v___x_4174_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__2;
                    if v_isShared_4172_ == 0 {
                        leanh::lean_ctor_set(v___x_4171_, 0, v___x_4174_);
                        v___x_4176_ = v___x_4171_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4177_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
                        v___x_4176_ = v_reuseFailAlloc_4177_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___x_4178_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__3;
                    if v_isShared_4172_ == 0 {
                        leanh::lean_ctor_set(v___x_4171_, 0, v___x_4178_);
                        v___x_4180_ = v___x_4171_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4181_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
                        v___x_4180_ = v_reuseFailAlloc_4181_;
                        state = 15;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_4176_;
            }
            15 => {
                return v___x_4180_;
            }
            16 => {
                if v_isShared_4186_ == 0 {
                    v___x_4188_ = v___x_4185_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4189_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
                    v___x_4188_ = v_reuseFailAlloc_4189_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4188_;
            }
            18 => {
                if v_isShared_4221_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4220_, 2);
                    v___x_4223_ = v___x_4220_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_val_4218_);
                    v___x_4223_ = v_reuseFailAlloc_4227_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_4224_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0;
                v___x_4225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4225_, 0, v___x_4223_);
                leanh::lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                v___x_4226_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4226_, 0, v___x_4225_);
                return v___x_4226_;
            }
            20 => {
                if v_isShared_4233_ == 0 {
                    v___x_4235_ = v___x_4232_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4236_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
                    v___x_4235_ = v_reuseFailAlloc_4236_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___boxed(
    mut v_e_4238_: *mut leanh::LeanObject,
    mut v_isMatch_4239_: *mut leanh::LeanObject,
    mut v_root_4240_: *mut leanh::LeanObject,
    mut v_a_4241_: *mut leanh::LeanObject,
    mut v_a_4242_: *mut leanh::LeanObject,
    mut v_a_4243_: *mut leanh::LeanObject,
    mut v_a_4244_: *mut leanh::LeanObject,
    mut v_a_4245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMatch_boxed_4246_: u8 = 0;
    let mut v_root_boxed_4247_: u8 = 0;
    let mut v_res_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMatch_boxed_4246_ = (leanh::lean_unbox(v_isMatch_4239_) as u8);
    v_root_boxed_4247_ = (leanh::lean_unbox(v_root_4240_) as u8);
    v_res_4248_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(
        v_e_4238_,
        v_isMatch_boxed_4246_,
        v_root_boxed_4247_,
        v_a_4241_,
        v_a_4242_,
        v_a_4243_,
        v_a_4244_,
    );
    leanh::lean_dec(v_a_4244_);
    leanh::lean_dec_ref(v_a_4243_);
    leanh::lean_dec(v_a_4242_);
    leanh::lean_dec_ref(v_a_4241_);
    return v_res_4248_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(
    mut v_declName_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
    mut v___y_4251_: *mut leanh::LeanObject,
    mut v___y_4252_: *mut leanh::LeanObject,
    mut v___y_4253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___redArg(v_declName_4249_, v___y_4253_);
    return v___x_4255_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0___boxed(
    mut v_declName_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
    mut v___y_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4262_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__0_spec__0(v_declName_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
    leanh::lean_dec(v___y_4260_);
    leanh::lean_dec_ref(v___y_4259_);
    leanh::lean_dec(v___y_4258_);
    leanh::lean_dec_ref(v___y_4257_);
    return v_res_4262_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(
    mut v_inst_4263_: *mut leanh::LeanObject,
    mut v_R_4264_: *mut leanh::LeanObject,
    mut v_a_4265_: *mut leanh::LeanObject,
    mut v_b_4266_: *mut leanh::LeanObject,
    mut v_c_4267_: *mut leanh::LeanObject,
    mut v___y_4268_: *mut leanh::LeanObject,
    mut v___y_4269_: *mut leanh::LeanObject,
    mut v___y_4270_: *mut leanh::LeanObject,
    mut v___y_4271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___redArg(v_a_4265_, v_b_4266_);
    return v___x_4273_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1___boxed(
    mut v_inst_4274_: *mut leanh::LeanObject,
    mut v_R_4275_: *mut leanh::LeanObject,
    mut v_a_4276_: *mut leanh::LeanObject,
    mut v_b_4277_: *mut leanh::LeanObject,
    mut v_c_4278_: *mut leanh::LeanObject,
    mut v___y_4279_: *mut leanh::LeanObject,
    mut v___y_4280_: *mut leanh::LeanObject,
    mut v___y_4281_: *mut leanh::LeanObject,
    mut v___y_4282_: *mut leanh::LeanObject,
    mut v___y_4283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4284_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs_spec__1(v_inst_4274_, v_R_4275_, v_a_4276_, v_b_4277_, v_c_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
    leanh::lean_dec(v___y_4282_);
    leanh::lean_dec_ref(v___y_4281_);
    leanh::lean_dec(v___y_4280_);
    leanh::lean_dec_ref(v___y_4279_);
    return v_res_4284_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(
    mut v_e_4285_: *mut leanh::LeanObject,
    mut v_root_4286_: u8,
    mut v_a_4287_: *mut leanh::LeanObject,
    mut v_a_4288_: *mut leanh::LeanObject,
    mut v_a_4289_: *mut leanh::LeanObject,
    mut v_a_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4292_: u8 = 0;
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = 1;
    v___x_4293_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(
        v_e_4285_,
        v___x_4292_,
        v_root_4286_,
        v_a_4287_,
        v_a_4288_,
        v_a_4289_,
        v_a_4290_,
    );
    return v___x_4293_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs___boxed(
    mut v_e_4294_: *mut leanh::LeanObject,
    mut v_root_4295_: *mut leanh::LeanObject,
    mut v_a_4296_: *mut leanh::LeanObject,
    mut v_a_4297_: *mut leanh::LeanObject,
    mut v_a_4298_: *mut leanh::LeanObject,
    mut v_a_4299_: *mut leanh::LeanObject,
    mut v_a_4300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_boxed_4301_: u8 = 0;
    let mut v_res_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_boxed_4301_ = (leanh::lean_unbox(v_root_4295_) as u8);
    v_res_4302_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchKeyArgs(
        v_e_4294_,
        v_root_boxed_4301_,
        v_a_4296_,
        v_a_4297_,
        v_a_4298_,
        v_a_4299_,
    );
    leanh::lean_dec(v_a_4299_);
    leanh::lean_dec_ref(v_a_4298_);
    leanh::lean_dec(v_a_4297_);
    leanh::lean_dec_ref(v_a_4296_);
    return v_res_4302_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(
    mut v_e_4303_: *mut leanh::LeanObject,
    mut v_root_4304_: u8,
    mut v_a_4305_: *mut leanh::LeanObject,
    mut v_a_4306_: *mut leanh::LeanObject,
    mut v_a_4307_: *mut leanh::LeanObject,
    mut v_a_4308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4310_ = 0;
    v___x_4311_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(
        v_e_4303_,
        v___x_4310_,
        v_root_4304_,
        v_a_4305_,
        v_a_4306_,
        v_a_4307_,
        v_a_4308_,
    );
    return v___x_4311_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs___boxed(
    mut v_e_4312_: *mut leanh::LeanObject,
    mut v_root_4313_: *mut leanh::LeanObject,
    mut v_a_4314_: *mut leanh::LeanObject,
    mut v_a_4315_: *mut leanh::LeanObject,
    mut v_a_4316_: *mut leanh::LeanObject,
    mut v_a_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_boxed_4319_: u8 = 0;
    let mut v_res_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_root_boxed_4319_ = (leanh::lean_unbox(v_root_4313_) as u8);
    v_res_4320_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnifyKeyArgs(
        v_e_4312_,
        v_root_boxed_4319_,
        v_a_4314_,
        v_a_4315_,
        v_a_4316_,
        v_a_4317_,
    );
    leanh::lean_dec(v_a_4317_);
    leanh::lean_dec_ref(v_a_4316_);
    leanh::lean_dec(v_a_4315_);
    leanh::lean_dec_ref(v_a_4314_);
    return v_res_4320_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(
    mut v_keys_4321_: *mut leanh::LeanObject,
    mut v_vals_4322_: *mut leanh::LeanObject,
    mut v_i_4323_: *mut leanh::LeanObject,
    mut v_k_4324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: u8 = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4325_ = lean_array_get_size(v_keys_4321_);
                v___x_4326_ = lean_nat_dec_lt(v_i_4323_, v___x_4325_);
                if v___x_4326_ == 0 {
                    leanh::lean_dec(v_i_4323_);
                    v___x_4327_ = leanh::lean_box(0);
                    return v___x_4327_;
                } else {
                    v_k_x27_4328_ = lean_array_fget_borrowed(v_keys_4321_, v_i_4323_);
                    v___x_4329_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_4324_, v_k_x27_4328_);
                    if v___x_4329_ == 0 {
                        v___x_4330_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4331_ = lean_nat_add(v_i_4323_, v___x_4330_);
                        leanh::lean_dec(v_i_4323_);
                        v_i_4323_ = v___x_4331_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4333_ = lean_array_fget_borrowed(v_vals_4322_, v_i_4323_);
                        leanh::lean_dec(v_i_4323_);
                        leanh::lean_inc(v___x_4333_);
                        v___x_4334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4334_, 0, v___x_4333_);
                        return v___x_4334_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_4335_: *mut leanh::LeanObject,
    mut v_vals_4336_: *mut leanh::LeanObject,
    mut v_i_4337_: *mut leanh::LeanObject,
    mut v_k_4338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4339_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_4335_, v_vals_4336_, v_i_4337_, v_k_4338_);
    leanh::lean_dec(v_k_4338_);
    leanh::lean_dec_ref(v_vals_4336_);
    leanh::lean_dec_ref(v_keys_4335_);
    return v_res_4339_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_4340_: usize = 0;
    let mut v___x_4341_: usize = 0;
    let mut v___x_4342_: usize = 0;
    v___x_4340_ = 5usize;
    v___x_4341_ = 1usize;
    v___x_4342_ = lean_usize_shift_left(v___x_4341_, v___x_4340_);
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_4343_: usize = 0;
    let mut v___x_4344_: usize = 0;
    let mut v___x_4345_: usize = 0;
    v___x_4343_ = 1usize;
    v___x_4344_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__0);
    v___x_4345_ = lean_usize_sub(v___x_4344_, v___x_4343_);
    return v___x_4345_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(
    mut v_x_4346_: *mut leanh::LeanObject,
    mut v_x_4347_: usize,
    mut v_x_4348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: usize = 0;
    let mut v___x_4352_: usize = 0;
    let mut v___x_4353_: usize = 0;
    let mut v_j_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: u8 = 0;
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: usize = 0;
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4346_) == 0 {
                    v_es_4349_ = leanh::lean_ctor_get(v_x_4346_, 0);
                    v___x_4350_ = leanh::lean_box(2);
                    v___x_4351_ = 5usize;
                    v___x_4352_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___closed__1);
                    v___x_4353_ = lean_usize_land(v_x_4347_, v___x_4352_);
                    v_j_4354_ = lean_usize_to_nat(v___x_4353_);
                    v___x_4355_ = lean_array_get_borrowed(v___x_4350_, v_es_4349_, v_j_4354_);
                    leanh::lean_dec(v_j_4354_);
                    match leanh::lean_obj_tag(v___x_4355_) {
                        0 => {
                            v_key_4356_ = leanh::lean_ctor_get(v___x_4355_, 0);
                            v_val_4357_ = leanh::lean_ctor_get(v___x_4355_, 1);
                            v___x_4358_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4348_, v_key_4356_);
                            if v___x_4358_ == 0 {
                                v___x_4359_ = leanh::lean_box(0);
                                return v___x_4359_;
                            } else {
                                leanh::lean_inc(v_val_4357_);
                                v___x_4360_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4360_, 0, v_val_4357_);
                                return v___x_4360_;
                            }
                        }
                        1 => {
                            v_node_4361_ = leanh::lean_ctor_get(v___x_4355_, 0);
                            v___x_4362_ = lean_usize_shift_right(v_x_4347_, v___x_4351_);
                            v_x_4346_ = v_node_4361_;
                            v_x_4347_ = v___x_4362_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4364_ = leanh::lean_box(0);
                            return v___x_4364_;
                        }
                    }
                } else {
                    v_ks_4365_ = leanh::lean_ctor_get(v_x_4346_, 0);
                    v_vs_4366_ = leanh::lean_ctor_get(v_x_4346_, 1);
                    v___x_4367_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4368_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_ks_4365_, v_vs_4366_, v___x_4367_, v_x_4348_);
                    return v___x_4368_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg___boxed(
    mut v_x_4369_: *mut leanh::LeanObject,
    mut v_x_4370_: *mut leanh::LeanObject,
    mut v_x_4371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_181__boxed_4372_: usize = 0;
    let mut v_res_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_181__boxed_4372_ = leanh::lean_unbox_usize(v_x_4370_);
    leanh::lean_dec(v_x_4370_);
    v_res_4373_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_4369_, v_x_181__boxed_4372_, v_x_4371_);
    leanh::lean_dec(v_x_4371_);
    leanh::lean_dec_ref(v_x_4369_);
    return v_res_4373_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(
    mut v_x_4374_: *mut leanh::LeanObject,
    mut v_x_4375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4376_: u64 = 0;
    let mut v___x_4377_: usize = 0;
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4375_);
    v___x_4377_ = lean_uint64_to_usize(v___x_4376_);
    v___x_4378_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_4374_, v___x_4377_, v_x_4375_);
    return v___x_4378_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg___boxed(
    mut v_x_4379_: *mut leanh::LeanObject,
    mut v_x_4380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4381_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_4379_, v_x_4380_);
    leanh::lean_dec(v_x_4380_);
    leanh::lean_dec_ref(v_x_4379_);
    return v_res_4381_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(
    mut v_d_4382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4383_ = leanh::lean_unsigned_to_nat(8);
    v_result_4384_ = lean_mk_empty_array_with_capacity(v___x_4383_);
    v___x_4385_ = leanh::lean_box(0);
    v___x_4386_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_4382_, v___x_4385_);
    if leanh::lean_obj_tag(v___x_4386_) == 0 {
        return v_result_4384_;
    } else {
        let mut v_val_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4387_ = leanh::lean_ctor_get(v___x_4386_, 0);
        leanh::lean_inc(v_val_4387_);
        leanh::lean_dec_ref_known(v___x_4386_, 1);
        v_vs_4388_ = leanh::lean_ctor_get(v_val_4387_, 0);
        leanh::lean_inc_ref(v_vs_4388_);
        leanh::lean_dec(v_val_4387_);
        v___x_4389_ = l_Array_append___redArg(v_result_4384_, v_vs_4388_);
        leanh::lean_dec_ref(v_vs_4388_);
        return v___x_4389_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg___boxed(
    mut v_d_4390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4391_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(
            v_d_4390_,
        );
    leanh::lean_dec_ref(v_d_4390_);
    return v_res_4391_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(
    mut v_00_u03b1_4392_: *mut leanh::LeanObject,
    mut v_d_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4394_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(
            v_d_4393_,
        );
    return v___x_4394_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___boxed(
    mut v_00_u03b1_4395_: *mut leanh::LeanObject,
    mut v_d_4396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4397_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult(
        v_00_u03b1_4395_,
        v_d_4396_,
    );
    leanh::lean_dec_ref(v_d_4396_);
    return v_res_4397_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(
    mut v_00_u03b2_4398_: *mut leanh::LeanObject,
    mut v_x_4399_: *mut leanh::LeanObject,
    mut v_x_4400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4401_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_x_4399_, v_x_4400_);
    return v___x_4401_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___boxed(
    mut v_00_u03b2_4402_: *mut leanh::LeanObject,
    mut v_x_4403_: *mut leanh::LeanObject,
    mut v_x_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4405_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0(v_00_u03b2_4402_, v_x_4403_, v_x_4404_);
    leanh::lean_dec(v_x_4404_);
    leanh::lean_dec_ref(v_x_4403_);
    return v_res_4405_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(
    mut v_00_u03b2_4406_: *mut leanh::LeanObject,
    mut v_x_4407_: *mut leanh::LeanObject,
    mut v_x_4408_: usize,
    mut v_x_4409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4410_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___redArg(v_x_4407_, v_x_4408_, v_x_4409_);
    return v___x_4410_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0___boxed(
    mut v_00_u03b2_4411_: *mut leanh::LeanObject,
    mut v_x_4412_: *mut leanh::LeanObject,
    mut v_x_4413_: *mut leanh::LeanObject,
    mut v_x_4414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_269__boxed_4415_: usize = 0;
    let mut v_res_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_269__boxed_4415_ = leanh::lean_unbox_usize(v_x_4413_);
    leanh::lean_dec(v_x_4413_);
    v_res_4416_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0(v_00_u03b2_4411_, v_x_4412_, v_x_269__boxed_4415_, v_x_4414_);
    leanh::lean_dec(v_x_4414_);
    leanh::lean_dec_ref(v_x_4412_);
    return v_res_4416_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4417_: *mut leanh::LeanObject,
    mut v_keys_4418_: *mut leanh::LeanObject,
    mut v_vals_4419_: *mut leanh::LeanObject,
    mut v_heq_4420_: *mut leanh::LeanObject,
    mut v_i_4421_: *mut leanh::LeanObject,
    mut v_k_4422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4423_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___redArg(v_keys_4418_, v_vals_4419_, v_i_4421_, v_k_4422_);
    return v___x_4423_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4424_: *mut leanh::LeanObject,
    mut v_keys_4425_: *mut leanh::LeanObject,
    mut v_vals_4426_: *mut leanh::LeanObject,
    mut v_heq_4427_: *mut leanh::LeanObject,
    mut v_i_4428_: *mut leanh::LeanObject,
    mut v_k_4429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4430_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0_spec__0_spec__1(v_00_u03b2_4424_, v_keys_4425_, v_vals_4426_, v_heq_4427_, v_i_4428_, v_k_4429_);
    leanh::lean_dec(v_k_4429_);
    leanh::lean_dec_ref(v_vals_4426_);
    leanh::lean_dec_ref(v_keys_4425_);
    return v_res_4430_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(
    mut v_a_4431_: *mut leanh::LeanObject,
    mut v_b_4432_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: u8 = 0;
    v_fst_4433_ = leanh::lean_ctor_get(v_a_4431_, 0);
    v_fst_4434_ = leanh::lean_ctor_get(v_b_4432_, 0);
    v___x_4435_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_4433_, v_fst_4434_);
    return v___x_4435_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0___boxed(
    mut v_a_4436_: *mut leanh::LeanObject,
    mut v_b_4437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4438_: u8 = 0;
    let mut v_r_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4438_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(
            v_a_4436_, v_b_4437_,
        );
    leanh::lean_dec_ref(v_b_4437_);
    leanh::lean_dec_ref(v_a_4436_);
    v_r_4439_ = leanh::lean_box((v_res_4438_) as usize);
    return v_r_4439_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(
    mut v_cs_4446_: *mut leanh::LeanObject,
    mut v_k_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: u8 = 0;
    v___x_4448_ = leanh::lean_unsigned_to_nat(0);
    v___x_4449_ = lean_array_get_size(v_cs_4446_);
    v___x_4450_ = lean_nat_dec_lt(v___x_4448_, v___x_4449_);
    if v___x_4450_ == 0 {
        let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_4447_);
        v___x_4451_ = leanh::lean_box(0);
        return v___x_4451_;
    } else {
        let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4454_: u8 = 0;
        v___x_4452_ = leanh::lean_unsigned_to_nat(1);
        v___x_4453_ = lean_nat_sub(v___x_4449_, v___x_4452_);
        v___x_4454_ = lean_nat_dec_le(v___x_4448_, v___x_4453_);
        if v___x_4454_ == 0 {
            let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_4453_);
            leanh::lean_dec(v_k_4447_);
            v___x_4455_ = leanh::lean_box(0);
            return v___x_4455_;
        } else {
            let mut v___f_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_4456_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0;
            v___x_4457_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2;
            v___x_4458_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4458_, 0, v_k_4447_);
            leanh::lean_ctor_set(v___x_4458_, 1, v___x_4457_);
            v___x_4459_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3;
            v___x_4460_ = l_Array_binSearchAux___redArg(
                v___f_4456_,
                v___x_4459_,
                v_cs_4446_,
                v___x_4458_,
                v___x_4448_,
                v___x_4453_,
            );
            return v___x_4460_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___boxed(
    mut v_cs_4461_: *mut leanh::LeanObject,
    mut v_k_4462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4463_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg(
        v_cs_4461_, v_k_4462_,
    );
    leanh::lean_dec_ref(v_cs_4461_);
    return v_res_4463_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(
    mut v_00_u03b1_4464_: *mut leanh::LeanObject,
    mut v_cs_4465_: *mut leanh::LeanObject,
    mut v_k_4466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: u8 = 0;
    v___x_4467_ = leanh::lean_unsigned_to_nat(0);
    v___x_4468_ = lean_array_get_size(v_cs_4465_);
    v___x_4469_ = lean_nat_dec_lt(v___x_4467_, v___x_4468_);
    if v___x_4469_ == 0 {
        let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_4466_);
        v___x_4470_ = leanh::lean_box(0);
        return v___x_4470_;
    } else {
        let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4473_: u8 = 0;
        v___x_4471_ = leanh::lean_unsigned_to_nat(1);
        v___x_4472_ = lean_nat_sub(v___x_4468_, v___x_4471_);
        v___x_4473_ = lean_nat_dec_le(v___x_4467_, v___x_4472_);
        if v___x_4473_ == 0 {
            let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_4472_);
            leanh::lean_dec(v_k_4466_);
            v___x_4474_ = leanh::lean_box(0);
            return v___x_4474_;
        } else {
            let mut v___f_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___f_4475_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__0;
            v___x_4476_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2;
            v___x_4477_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_4477_, 0, v_k_4466_);
            leanh::lean_ctor_set(v___x_4477_, 1, v___x_4476_);
            v___x_4478_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__3;
            v___x_4479_ = l_Array_binSearchAux___redArg(
                v___f_4475_,
                v___x_4478_,
                v_cs_4465_,
                v___x_4477_,
                v___x_4467_,
                v___x_4472_,
            );
            return v___x_4479_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___boxed(
    mut v_00_u03b1_4480_: *mut leanh::LeanObject,
    mut v_cs_4481_: *mut leanh::LeanObject,
    mut v_k_4482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4483_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey(
        v_00_u03b1_4480_,
        v_cs_4481_,
        v_k_4482_,
    );
    leanh::lean_dec_ref(v_cs_4481_);
    return v_res_4483_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(
    mut v_as_4484_: *mut leanh::LeanObject,
    mut v_k_4485_: *mut leanh::LeanObject,
    mut v_x_4486_: *mut leanh::LeanObject,
    mut v_x_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: u8 = 0;
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: u8 = 0;
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4488_ = lean_nat_add(v_x_4486_, v_x_4487_);
                v___x_4489_ = leanh::lean_unsigned_to_nat(1);
                v_m_4490_ = lean_nat_shiftr(v___x_4488_, v___x_4489_);
                leanh::lean_dec(v___x_4488_);
                v_a_4491_ = lean_array_fget_borrowed(v_as_4484_, v_m_4490_);
                v___x_4492_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_a_4491_, v_k_4485_);
                if v___x_4492_ == 0 {
                    leanh::lean_dec(v_x_4487_);
                    v___x_4493_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___lam__0(v_k_4485_, v_a_4491_);
                    if v___x_4493_ == 0 {
                        leanh::lean_dec(v_m_4490_);
                        leanh::lean_dec(v_x_4486_);
                        leanh::lean_inc(v_a_4491_);
                        v___x_4494_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4494_, 0, v_a_4491_);
                        return v___x_4494_;
                    } else {
                        v___x_4495_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4496_ = lean_nat_dec_eq(v_m_4490_, v___x_4495_);
                        if v___x_4496_ == 0 {
                            v___x_4497_ = lean_nat_sub(v_m_4490_, v___x_4489_);
                            leanh::lean_dec(v_m_4490_);
                            v___x_4498_ = lean_nat_dec_lt(v___x_4497_, v_x_4486_);
                            if v___x_4498_ == 0 {
                                v_x_4487_ = v___x_4497_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_4497_);
                                leanh::lean_dec(v_x_4486_);
                                v___x_4500_ = leanh::lean_box(0);
                                return v___x_4500_;
                            }
                        } else {
                            leanh::lean_dec(v_m_4490_);
                            leanh::lean_dec(v_x_4486_);
                            v___x_4501_ = leanh::lean_box(0);
                            return v___x_4501_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_4486_);
                    v___x_4502_ = lean_nat_add(v_m_4490_, v___x_4489_);
                    leanh::lean_dec(v_m_4490_);
                    v___x_4503_ = lean_nat_dec_le(v___x_4502_, v_x_4487_);
                    if v___x_4503_ == 0 {
                        leanh::lean_dec(v___x_4502_);
                        leanh::lean_dec(v_x_4487_);
                        v___x_4504_ = leanh::lean_box(0);
                        return v___x_4504_;
                    } else {
                        v_x_4486_ = v___x_4502_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg___boxed(
    mut v_as_4506_: *mut leanh::LeanObject,
    mut v_k_4507_: *mut leanh::LeanObject,
    mut v_x_4508_: *mut leanh::LeanObject,
    mut v_x_4509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4510_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_4506_, v_k_4507_, v_x_4508_, v_x_4509_);
    leanh::lean_dec_ref(v_k_4507_);
    leanh::lean_dec_ref(v_as_4506_);
    return v_res_4510_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4511_ = l_Lean_Meta_DiscrTree_instInhabitedTrie(leanh::lean_box(0));
    return v___x_4511_;
}
pub unsafe fn _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4512_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0_once), _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__0);
    v___x_4513_ = leanh::lean_box(0);
    v___x_4514_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4514_, 0, v___x_4513_);
    leanh::lean_ctor_set(v___x_4514_, 1, v___x_4512_);
    return v___x_4514_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(
    mut v_todo_4515_: *mut leanh::LeanObject,
    mut v_c_4516_: *mut leanh::LeanObject,
    mut v_result_4517_: *mut leanh::LeanObject,
    mut v_a_4518_: *mut leanh::LeanObject,
    mut v_a_4519_: *mut leanh::LeanObject,
    mut v_a_4520_: *mut leanh::LeanObject,
    mut v_a_4521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: u8 = 0;
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: u8 = 0;
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4539_: u8 = 0;
    let mut v_fst_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_first_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v_todo_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: u8 = 0;
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: u8 = 0;
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut v_isSharedCheck_4573_: u8 = 0;
    let mut v_a_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4581_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_4523_ = leanh::lean_ctor_get(v_c_4516_, 0);
                leanh::lean_inc_ref(v_vs_4523_);
                v_children_4524_ = leanh::lean_ctor_get(v_c_4516_, 1);
                leanh::lean_inc_ref(v_children_4524_);
                leanh::lean_dec_ref(v_c_4516_);
                v___x_4525_ = lean_array_get_size(v_todo_4515_);
                v___x_4526_ = leanh::lean_unsigned_to_nat(0);
                v___x_4527_ = lean_nat_dec_eq(v___x_4525_, v___x_4526_);
                if v___x_4527_ == 0 {
                    leanh::lean_dec_ref(v_vs_4523_);
                    v___x_4528_ = lean_array_get_size(v_children_4524_);
                    v___x_4529_ = lean_nat_dec_eq(v___x_4528_, v___x_4526_);
                    if v___x_4529_ == 0 {
                        v___x_4530_ = l_Lean_instInhabitedExpr;
                        v___x_4531_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4532_ = lean_nat_sub(v___x_4525_, v___x_4531_);
                        v_e_4533_ = lean_array_get_borrowed(v___x_4530_, v_todo_4515_, v___x_4532_);
                        leanh::lean_dec(v___x_4532_);
                        v___x_4534_ = 1;
                        leanh::lean_inc(v_e_4533_);
                        v___x_4535_ =
                            l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(
                                v_e_4533_,
                                v___x_4534_,
                                v___x_4529_,
                                v_a_4518_,
                                v_a_4519_,
                                v_a_4520_,
                                v_a_4521_,
                            );
                        if leanh::lean_obj_tag(v___x_4535_) == 0 {
                            v_a_4536_ = leanh::lean_ctor_get(v___x_4535_, 0);
                            v_isSharedCheck_4573_ =
                                (!leanh::lean_is_exclusive(v___x_4535_)) as u8;
                            if v_isSharedCheck_4573_ == 0 {
                                v___x_4538_ = v___x_4535_;
                                v_isShared_4539_ = v_isSharedCheck_4573_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4536_);
                                leanh::lean_dec(v___x_4535_);
                                v___x_4538_ = leanh::lean_box(0);
                                v_isShared_4539_ = v_isSharedCheck_4573_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_children_4524_);
                            leanh::lean_dec_ref(v_result_4517_);
                            leanh::lean_dec_ref(v_todo_4515_);
                            v_a_4574_ = leanh::lean_ctor_get(v___x_4535_, 0);
                            v_isSharedCheck_4581_ =
                                (!leanh::lean_is_exclusive(v___x_4535_)) as u8;
                            if v_isSharedCheck_4581_ == 0 {
                                v___x_4576_ = v___x_4535_;
                                v_isShared_4577_ = v_isSharedCheck_4581_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4574_);
                                leanh::lean_dec(v___x_4535_);
                                v___x_4576_ = leanh::lean_box(0);
                                v_isShared_4577_ = v_isSharedCheck_4581_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_children_4524_);
                        leanh::lean_dec_ref(v_todo_4515_);
                        v___x_4582_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4582_, 0, v_result_4517_);
                        return v___x_4582_;
                    }
                } else {
                    leanh::lean_dec_ref(v_children_4524_);
                    leanh::lean_dec_ref(v_todo_4515_);
                    v___x_4583_ = l_Array_append___redArg(v_result_4517_, v_vs_4523_);
                    leanh::lean_dec_ref(v_vs_4523_);
                    v___x_4584_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4584_, 0, v___x_4583_);
                    return v___x_4584_;
                }
            }
            1 => {
                v_fst_4540_ = leanh::lean_ctor_get(v_a_4536_, 0);
                leanh::lean_inc(v_fst_4540_);
                v_snd_4541_ = leanh::lean_ctor_get(v_a_4536_, 1);
                leanh::lean_inc(v_snd_4541_);
                leanh::lean_dec(v_a_4536_);
                v___x_4542_ = leanh::lean_box(0);
                v___x_4543_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once), _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
                v_first_4544_ = lean_array_get(v___x_4543_, v_children_4524_, v___x_4526_);
                v_fst_4545_ = leanh::lean_ctor_get(v_first_4544_, 0);
                v_snd_4546_ = leanh::lean_ctor_get(v_first_4544_, 1);
                v_isSharedCheck_4572_ = (!leanh::lean_is_exclusive(v_first_4544_)) as u8;
                if v_isSharedCheck_4572_ == 0 {
                    v___x_4548_ = v_first_4544_;
                    v_isShared_4549_ = v_isSharedCheck_4572_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4546_);
                    leanh::lean_inc(v_fst_4545_);
                    leanh::lean_dec(v_first_4544_);
                    v___x_4548_ = leanh::lean_box(0);
                    v_isShared_4549_ = v_isSharedCheck_4572_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_todo_4550_ = lean_array_pop(v_todo_4515_);
                v___x_4566_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_4545_, v___x_4542_);
                leanh::lean_dec(v_fst_4545_);
                if v___x_4566_ == 0 {
                    leanh::lean_dec(v_snd_4546_);
                    leanh::lean_inc_ref(v_result_4517_);
                    if v_isShared_4539_ == 0 {
                        leanh::lean_ctor_set(v___x_4538_, 0, v_result_4517_);
                        v___x_4568_ = v___x_4538_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_result_4517_);
                        v___x_4568_ = v_reuseFailAlloc_4569_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4538_);
                    leanh::lean_inc_ref(v_todo_4550_);
                    v___x_4570_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(v_todo_4550_, v_snd_4546_, v_result_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
                    if leanh::lean_obj_tag(v___x_4570_) == 0 {
                        v_a_4571_ = leanh::lean_ctor_get(v___x_4570_, 0);
                        leanh::lean_inc(v_a_4571_);
                        v___y_4552_ = v___x_4570_;
                        v_a_4553_ = v_a_4571_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_todo_4550_);
                        leanh::lean_del_object(v___x_4548_);
                        leanh::lean_dec(v_snd_4541_);
                        leanh::lean_dec(v_fst_4540_);
                        leanh::lean_dec_ref(v_children_4524_);
                        return v___x_4570_;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_fst_4540_) == 0 {
                    leanh::lean_dec_ref(v_a_4553_);
                    leanh::lean_dec_ref(v_todo_4550_);
                    leanh::lean_del_object(v___x_4548_);
                    leanh::lean_dec(v_snd_4541_);
                    leanh::lean_dec_ref(v_children_4524_);
                    return v___y_4552_;
                } else {
                    v___x_4554_ = lean_nat_dec_lt(v___x_4526_, v___x_4528_);
                    if v___x_4554_ == 0 {
                        leanh::lean_dec_ref(v_a_4553_);
                        leanh::lean_dec_ref(v_todo_4550_);
                        leanh::lean_del_object(v___x_4548_);
                        leanh::lean_dec(v_snd_4541_);
                        leanh::lean_dec(v_fst_4540_);
                        leanh::lean_dec_ref(v_children_4524_);
                        return v___y_4552_;
                    } else {
                        v___x_4555_ = lean_nat_sub(v___x_4528_, v___x_4531_);
                        v___x_4556_ = lean_nat_dec_le(v___x_4526_, v___x_4555_);
                        if v___x_4556_ == 0 {
                            leanh::lean_dec(v___x_4555_);
                            leanh::lean_dec_ref(v_a_4553_);
                            leanh::lean_dec_ref(v_todo_4550_);
                            leanh::lean_del_object(v___x_4548_);
                            leanh::lean_dec(v_snd_4541_);
                            leanh::lean_dec(v_fst_4540_);
                            leanh::lean_dec_ref(v_children_4524_);
                            return v___y_4552_;
                        } else {
                            v___x_4557_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2;
                            if v_isShared_4549_ == 0 {
                                leanh::lean_ctor_set(v___x_4548_, 1, v___x_4557_);
                                leanh::lean_ctor_set(v___x_4548_, 0, v_fst_4540_);
                                v___x_4559_ = v___x_4548_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_4565_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_fst_4540_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4565_, 1, v___x_4557_);
                                v___x_4559_ = v_reuseFailAlloc_4565_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_4560_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_4524_, v___x_4559_, v___x_4526_, v___x_4555_);
                leanh::lean_dec_ref(v___x_4559_);
                leanh::lean_dec_ref(v_children_4524_);
                if leanh::lean_obj_tag(v___x_4560_) == 0 {
                    leanh::lean_dec_ref(v_a_4553_);
                    leanh::lean_dec_ref(v_todo_4550_);
                    leanh::lean_dec(v_snd_4541_);
                    return v___y_4552_;
                } else {
                    leanh::lean_dec_ref(v___y_4552_);
                    v_val_4561_ = leanh::lean_ctor_get(v___x_4560_, 0);
                    leanh::lean_inc(v_val_4561_);
                    leanh::lean_dec_ref_known(v___x_4560_, 1);
                    v_snd_4562_ = leanh::lean_ctor_get(v_val_4561_, 1);
                    leanh::lean_inc(v_snd_4562_);
                    leanh::lean_dec(v_val_4561_);
                    v___x_4563_ = l_Array_append___redArg(v_todo_4550_, v_snd_4541_);
                    leanh::lean_dec(v_snd_4541_);
                    v_todo_4515_ = v___x_4563_;
                    v_c_4516_ = v_snd_4562_;
                    v_result_4517_ = v_a_4553_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                v___y_4552_ = v___x_4568_;
                v_a_4553_ = v_result_4517_;
                state = 3;
                continue;
            }
            6 => {
                if v_isShared_4577_ == 0 {
                    v___x_4579_ = v___x_4576_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
                    v___x_4579_ = v_reuseFailAlloc_4580_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4579_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___boxed(
    mut v_todo_4585_: *mut leanh::LeanObject,
    mut v_c_4586_: *mut leanh::LeanObject,
    mut v_result_4587_: *mut leanh::LeanObject,
    mut v_a_4588_: *mut leanh::LeanObject,
    mut v_a_4589_: *mut leanh::LeanObject,
    mut v_a_4590_: *mut leanh::LeanObject,
    mut v_a_4591_: *mut leanh::LeanObject,
    mut v_a_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4593_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(
        v_todo_4585_,
        v_c_4586_,
        v_result_4587_,
        v_a_4588_,
        v_a_4589_,
        v_a_4590_,
        v_a_4591_,
    );
    leanh::lean_dec(v_a_4591_);
    leanh::lean_dec_ref(v_a_4590_);
    leanh::lean_dec(v_a_4589_);
    leanh::lean_dec_ref(v_a_4588_);
    return v_res_4593_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(
    mut v_00_u03b1_4594_: *mut leanh::LeanObject,
    mut v_todo_4595_: *mut leanh::LeanObject,
    mut v_c_4596_: *mut leanh::LeanObject,
    mut v_result_4597_: *mut leanh::LeanObject,
    mut v_a_4598_: *mut leanh::LeanObject,
    mut v_a_4599_: *mut leanh::LeanObject,
    mut v_a_4600_: *mut leanh::LeanObject,
    mut v_a_4601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4603_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(
        v_todo_4595_,
        v_c_4596_,
        v_result_4597_,
        v_a_4598_,
        v_a_4599_,
        v_a_4600_,
        v_a_4601_,
    );
    return v___x_4603_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___boxed(
    mut v_00_u03b1_4604_: *mut leanh::LeanObject,
    mut v_todo_4605_: *mut leanh::LeanObject,
    mut v_c_4606_: *mut leanh::LeanObject,
    mut v_result_4607_: *mut leanh::LeanObject,
    mut v_a_4608_: *mut leanh::LeanObject,
    mut v_a_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
    mut v_a_4611_: *mut leanh::LeanObject,
    mut v_a_4612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4613_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop(
        v_00_u03b1_4604_,
        v_todo_4605_,
        v_c_4606_,
        v_result_4607_,
        v_a_4608_,
        v_a_4609_,
        v_a_4610_,
        v_a_4611_,
    );
    leanh::lean_dec(v_a_4611_);
    leanh::lean_dec_ref(v_a_4610_);
    leanh::lean_dec(v_a_4609_);
    leanh::lean_dec_ref(v_a_4608_);
    return v_res_4613_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(
    mut v_00_u03b1_4614_: *mut leanh::LeanObject,
    mut v_as_4615_: *mut leanh::LeanObject,
    mut v_k_4616_: *mut leanh::LeanObject,
    mut v_x_4617_: *mut leanh::LeanObject,
    mut v_x_4618_: *mut leanh::LeanObject,
    mut v_x_4619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_as_4615_, v_k_4616_, v_x_4617_, v_x_4618_);
    return v___x_4620_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___boxed(
    mut v_00_u03b1_4621_: *mut leanh::LeanObject,
    mut v_as_4622_: *mut leanh::LeanObject,
    mut v_k_4623_: *mut leanh::LeanObject,
    mut v_x_4624_: *mut leanh::LeanObject,
    mut v_x_4625_: *mut leanh::LeanObject,
    mut v_x_4626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4627_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0(v_00_u03b1_4621_, v_as_4622_, v_k_4623_, v_x_4624_, v_x_4625_, v_x_4626_);
    leanh::lean_dec_ref(v_k_4623_);
    leanh::lean_dec_ref(v_as_4622_);
    return v_res_4627_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(
    mut v_d_4628_: *mut leanh::LeanObject,
    mut v_k_4629_: *mut leanh::LeanObject,
    mut v_args_4630_: *mut leanh::LeanObject,
    mut v_result_4631_: *mut leanh::LeanObject,
    mut v_a_4632_: *mut leanh::LeanObject,
    mut v_a_4633_: *mut leanh::LeanObject,
    mut v_a_4634_: *mut leanh::LeanObject,
    mut v_a_4635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_4628_, v_k_4629_);
    if leanh::lean_obj_tag(v___x_4637_) == 0 {
        let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_args_4630_);
        v___x_4638_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4638_, 0, v_result_4631_);
        return v___x_4638_;
    } else {
        let mut v_val_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4639_ = leanh::lean_ctor_get(v___x_4637_, 0);
        leanh::lean_inc(v_val_4639_);
        leanh::lean_dec_ref_known(v___x_4637_, 1);
        v___x_4640_ =
            l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg(
                v_args_4630_,
                v_val_4639_,
                v_result_4631_,
                v_a_4632_,
                v_a_4633_,
                v_a_4634_,
                v_a_4635_,
            );
        return v___x_4640_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg___boxed(
    mut v_d_4641_: *mut leanh::LeanObject,
    mut v_k_4642_: *mut leanh::LeanObject,
    mut v_args_4643_: *mut leanh::LeanObject,
    mut v_result_4644_: *mut leanh::LeanObject,
    mut v_a_4645_: *mut leanh::LeanObject,
    mut v_a_4646_: *mut leanh::LeanObject,
    mut v_a_4647_: *mut leanh::LeanObject,
    mut v_a_4648_: *mut leanh::LeanObject,
    mut v_a_4649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4650_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(
        v_d_4641_,
        v_k_4642_,
        v_args_4643_,
        v_result_4644_,
        v_a_4645_,
        v_a_4646_,
        v_a_4647_,
        v_a_4648_,
    );
    leanh::lean_dec(v_a_4648_);
    leanh::lean_dec_ref(v_a_4647_);
    leanh::lean_dec(v_a_4646_);
    leanh::lean_dec_ref(v_a_4645_);
    leanh::lean_dec(v_k_4642_);
    leanh::lean_dec_ref(v_d_4641_);
    return v_res_4650_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(
    mut v_00_u03b1_4651_: *mut leanh::LeanObject,
    mut v_d_4652_: *mut leanh::LeanObject,
    mut v_k_4653_: *mut leanh::LeanObject,
    mut v_args_4654_: *mut leanh::LeanObject,
    mut v_result_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
    mut v_a_4659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(
        v_d_4652_,
        v_k_4653_,
        v_args_4654_,
        v_result_4655_,
        v_a_4656_,
        v_a_4657_,
        v_a_4658_,
        v_a_4659_,
    );
    return v___x_4661_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___boxed(
    mut v_00_u03b1_4662_: *mut leanh::LeanObject,
    mut v_d_4663_: *mut leanh::LeanObject,
    mut v_k_4664_: *mut leanh::LeanObject,
    mut v_args_4665_: *mut leanh::LeanObject,
    mut v_result_4666_: *mut leanh::LeanObject,
    mut v_a_4667_: *mut leanh::LeanObject,
    mut v_a_4668_: *mut leanh::LeanObject,
    mut v_a_4669_: *mut leanh::LeanObject,
    mut v_a_4670_: *mut leanh::LeanObject,
    mut v_a_4671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4672_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot(
        v_00_u03b1_4662_,
        v_d_4663_,
        v_k_4664_,
        v_args_4665_,
        v_result_4666_,
        v_a_4667_,
        v_a_4668_,
        v_a_4669_,
        v_a_4670_,
    );
    leanh::lean_dec(v_a_4670_);
    leanh::lean_dec_ref(v_a_4669_);
    leanh::lean_dec(v_a_4668_);
    leanh::lean_dec_ref(v_a_4667_);
    leanh::lean_dec(v_k_4664_);
    leanh::lean_dec_ref(v_d_4663_);
    return v_res_4672_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(
    mut v_d_4673_: *mut leanh::LeanObject,
    mut v_e_4674_: *mut leanh::LeanObject,
    mut v_a_4675_: *mut leanh::LeanObject,
    mut v_a_4676_: *mut leanh::LeanObject,
    mut v_a_4677_: *mut leanh::LeanObject,
    mut v_a_4678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4681_: u8 = 0;
    let mut v_ctxApprox_4682_: u8 = 0;
    let mut v_quasiPatternApprox_4683_: u8 = 0;
    let mut v_constApprox_4684_: u8 = 0;
    let mut v_isDefEqStuckEx_4685_: u8 = 0;
    let mut v_unificationHints_4686_: u8 = 0;
    let mut v_proofIrrelevance_4687_: u8 = 0;
    let mut v_assignSyntheticOpaque_4688_: u8 = 0;
    let mut v_offsetCnstrs_4689_: u8 = 0;
    let mut v_etaStruct_4690_: u8 = 0;
    let mut v_univApprox_4691_: u8 = 0;
    let mut v_iota_4692_: u8 = 0;
    let mut v_beta_4693_: u8 = 0;
    let mut v_proj_4694_: u8 = 0;
    let mut v_zeta_4695_: u8 = 0;
    let mut v_zetaDelta_4696_: u8 = 0;
    let mut v_zetaUnused_4697_: u8 = 0;
    let mut v_zetaHave_4698_: u8 = 0;
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v_trackZetaDelta_4702_: u8 = 0;
    let mut v_zetaDeltaSet_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4709_: u8 = 0;
    let mut v_inTypeClassResolution_4710_: u8 = 0;
    let mut v_cacheInferType_4711_: u8 = 0;
    let mut v___x_4712_: u8 = 0;
    let mut v_config_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: u64 = 0;
    let mut v___x_4716_: u64 = 0;
    let mut v___x_4717_: u64 = 0;
    let mut v___x_4718_: u8 = 0;
    let mut v___x_4719_: u64 = 0;
    let mut v___x_4720_: u64 = 0;
    let mut v_key_4721_: u64 = 0;
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4728_: u8 = 0;
    let mut v_fst_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4733_: u8 = 0;
    let mut v_result_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4745_: u8 = 0;
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4752_: u8 = 0;
    let mut v_a_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4756_: u8 = 0;
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4760_: u8 = 0;
    let mut v_isSharedCheck_4761_: u8 = 0;
    let mut v_isSharedCheck_4762_: u8 = 0;
    let mut v_a_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4766_: u8 = 0;
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4770_: u8 = 0;
    let mut v_reuseFailAlloc_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4680_ = l_Lean_Meta_Context_config(v_a_4675_);
                v_foApprox_4681_ = leanh::lean_ctor_get_uint8(v___x_4680_, 0 as u32);
                v_ctxApprox_4682_ = leanh::lean_ctor_get_uint8(v___x_4680_, 1 as u32);
                v_quasiPatternApprox_4683_ =
                    leanh::lean_ctor_get_uint8(v___x_4680_, 2 as u32);
                v_constApprox_4684_ = leanh::lean_ctor_get_uint8(v___x_4680_, 3 as u32);
                v_isDefEqStuckEx_4685_ = leanh::lean_ctor_get_uint8(v___x_4680_, 4 as u32);
                v_unificationHints_4686_ = leanh::lean_ctor_get_uint8(v___x_4680_, 5 as u32);
                v_proofIrrelevance_4687_ = leanh::lean_ctor_get_uint8(v___x_4680_, 6 as u32);
                v_assignSyntheticOpaque_4688_ =
                    leanh::lean_ctor_get_uint8(v___x_4680_, 7 as u32);
                v_offsetCnstrs_4689_ = leanh::lean_ctor_get_uint8(v___x_4680_, 8 as u32);
                v_etaStruct_4690_ = leanh::lean_ctor_get_uint8(v___x_4680_, 10 as u32);
                v_univApprox_4691_ = leanh::lean_ctor_get_uint8(v___x_4680_, 11 as u32);
                v_iota_4692_ = leanh::lean_ctor_get_uint8(v___x_4680_, 12 as u32);
                v_beta_4693_ = leanh::lean_ctor_get_uint8(v___x_4680_, 13 as u32);
                v_proj_4694_ = leanh::lean_ctor_get_uint8(v___x_4680_, 14 as u32);
                v_zeta_4695_ = leanh::lean_ctor_get_uint8(v___x_4680_, 15 as u32);
                v_zetaDelta_4696_ = leanh::lean_ctor_get_uint8(v___x_4680_, 16 as u32);
                v_zetaUnused_4697_ = leanh::lean_ctor_get_uint8(v___x_4680_, 17 as u32);
                v_zetaHave_4698_ = leanh::lean_ctor_get_uint8(v___x_4680_, 18 as u32);
                v_isSharedCheck_4772_ = (!leanh::lean_is_exclusive(v___x_4680_)) as u8;
                if v_isSharedCheck_4772_ == 0 {
                    v___x_4700_ = v___x_4680_;
                    v_isShared_4701_ = v_isSharedCheck_4772_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4680_);
                    v___x_4700_ = leanh::lean_box(0);
                    v_isShared_4701_ = v_isSharedCheck_4772_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_4702_ = leanh::lean_ctor_get_uint8(
                    v_a_4675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4703_ = leanh::lean_ctor_get(v_a_4675_, 1);
                v_lctx_4704_ = leanh::lean_ctor_get(v_a_4675_, 2);
                v_localInstances_4705_ = leanh::lean_ctor_get(v_a_4675_, 3);
                v_defEqCtx_x3f_4706_ = leanh::lean_ctor_get(v_a_4675_, 4);
                v_synthPendingDepth_4707_ = leanh::lean_ctor_get(v_a_4675_, 5);
                v_canUnfold_x3f_4708_ = leanh::lean_ctor_get(v_a_4675_, 6);
                v_univApprox_4709_ = leanh::lean_ctor_get_uint8(
                    v_a_4675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4710_ = leanh::lean_ctor_get_uint8(
                    v_a_4675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4711_ = leanh::lean_ctor_get_uint8(
                    v_a_4675_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_4712_ = 2;
                if v_isShared_4701_ == 0 {
                    v_config_4714_ = v___x_4700_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4771_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        0 as u32,
                        v_foApprox_4681_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        1 as u32,
                        v_ctxApprox_4682_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        2 as u32,
                        v_quasiPatternApprox_4683_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        3 as u32,
                        v_constApprox_4684_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        4 as u32,
                        v_isDefEqStuckEx_4685_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        5 as u32,
                        v_unificationHints_4686_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        6 as u32,
                        v_proofIrrelevance_4687_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        7 as u32,
                        v_assignSyntheticOpaque_4688_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        8 as u32,
                        v_offsetCnstrs_4689_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        10 as u32,
                        v_etaStruct_4690_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        11 as u32,
                        v_univApprox_4691_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        12 as u32,
                        v_iota_4692_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        13 as u32,
                        v_beta_4693_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        14 as u32,
                        v_proj_4694_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        15 as u32,
                        v_zeta_4695_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        16 as u32,
                        v_zetaDelta_4696_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        17 as u32,
                        v_zetaUnused_4697_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4771_,
                        18 as u32,
                        v_zetaHave_4698_,
                    );
                    v_config_4714_ = v_reuseFailAlloc_4771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_4714_, 9 as u32, v___x_4712_);
                v___x_4715_ = l_Lean_Meta_Context_configKey(v_a_4675_);
                v___x_4716_ = 3u64;
                v___x_4717_ = lean_uint64_shift_right(v___x_4715_, v___x_4716_);
                v___x_4718_ = 1;
                v___x_4719_ = lean_uint64_shift_left(v___x_4717_, v___x_4716_);
                v___x_4720_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0_once),
                    _init_l_Lean_Meta_DiscrTree_mkPath___closed__0,
                );
                v_key_4721_ = lean_uint64_lor(v___x_4719_, v___x_4720_);
                v___x_4722_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_4722_, 0, v_config_4714_);
                leanh::lean_ctor_set_uint64(
                    v___x_4722_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_4721_,
                );
                leanh::lean_inc(v_canUnfold_x3f_4708_);
                leanh::lean_inc(v_synthPendingDepth_4707_);
                leanh::lean_inc(v_defEqCtx_x3f_4706_);
                leanh::lean_inc_ref(v_localInstances_4705_);
                leanh::lean_inc_ref(v_lctx_4704_);
                leanh::lean_inc(v_zetaDeltaSet_4703_);
                v___x_4723_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_4723_, 0, v___x_4722_);
                leanh::lean_ctor_set(v___x_4723_, 1, v_zetaDeltaSet_4703_);
                leanh::lean_ctor_set(v___x_4723_, 2, v_lctx_4704_);
                leanh::lean_ctor_set(v___x_4723_, 3, v_localInstances_4705_);
                leanh::lean_ctor_set(v___x_4723_, 4, v_defEqCtx_x3f_4706_);
                leanh::lean_ctor_set(v___x_4723_, 5, v_synthPendingDepth_4707_);
                leanh::lean_ctor_set(v___x_4723_, 6, v_canUnfold_x3f_4708_);
                leanh::lean_ctor_set_uint8(
                    v___x_4723_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4702_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4723_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4709_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4723_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4710_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4723_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4711_,
                );
                v___x_4724_ =
                    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(
                        v_e_4674_,
                        v___x_4718_,
                        v___x_4718_,
                        v___x_4723_,
                        v_a_4676_,
                        v_a_4677_,
                        v_a_4678_,
                    );
                if leanh::lean_obj_tag(v___x_4724_) == 0 {
                    v_a_4725_ = leanh::lean_ctor_get(v___x_4724_, 0);
                    v_isSharedCheck_4762_ = (!leanh::lean_is_exclusive(v___x_4724_)) as u8;
                    if v_isSharedCheck_4762_ == 0 {
                        v___x_4727_ = v___x_4724_;
                        v_isShared_4728_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4725_);
                        leanh::lean_dec(v___x_4724_);
                        v___x_4727_ = leanh::lean_box(0);
                        v_isShared_4728_ = v_isSharedCheck_4762_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_4723_, 7);
                    v_a_4763_ = leanh::lean_ctor_get(v___x_4724_, 0);
                    v_isSharedCheck_4770_ = (!leanh::lean_is_exclusive(v___x_4724_)) as u8;
                    if v_isSharedCheck_4770_ == 0 {
                        v___x_4765_ = v___x_4724_;
                        v_isShared_4766_ = v_isSharedCheck_4770_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4763_);
                        leanh::lean_dec(v___x_4724_);
                        v___x_4765_ = leanh::lean_box(0);
                        v_isShared_4766_ = v_isSharedCheck_4770_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_4729_ = leanh::lean_ctor_get(v_a_4725_, 0);
                v_snd_4730_ = leanh::lean_ctor_get(v_a_4725_, 1);
                v_isSharedCheck_4761_ = (!leanh::lean_is_exclusive(v_a_4725_)) as u8;
                if v_isSharedCheck_4761_ == 0 {
                    v___x_4732_ = v_a_4725_;
                    v_isShared_4733_ = v_isSharedCheck_4761_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4730_);
                    leanh::lean_inc(v_fst_4729_);
                    leanh::lean_dec(v_a_4725_);
                    v___x_4732_ = leanh::lean_box(0);
                    v_isShared_4733_ = v_isSharedCheck_4761_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_result_4734_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_4673_);
                if leanh::lean_obj_tag(v_fst_4729_) == 0 {
                    leanh::lean_dec(v_snd_4730_);
                    leanh::lean_dec_ref_known(v___x_4723_, 7);
                    if v_isShared_4733_ == 0 {
                        leanh::lean_ctor_set(v___x_4732_, 1, v_result_4734_);
                        v___x_4736_ = v___x_4732_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4740_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_fst_4729_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4740_, 1, v_result_4734_);
                        v___x_4736_ = v_reuseFailAlloc_4740_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4727_);
                    v___x_4741_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchRoot___redArg(v_d_4673_, v_fst_4729_, v_snd_4730_, v_result_4734_, v___x_4723_, v_a_4676_, v_a_4677_, v_a_4678_);
                    leanh::lean_dec_ref_known(v___x_4723_, 7);
                    if leanh::lean_obj_tag(v___x_4741_) == 0 {
                        v_a_4742_ = leanh::lean_ctor_get(v___x_4741_, 0);
                        v_isSharedCheck_4752_ =
                            (!leanh::lean_is_exclusive(v___x_4741_)) as u8;
                        if v_isSharedCheck_4752_ == 0 {
                            v___x_4744_ = v___x_4741_;
                            v_isShared_4745_ = v_isSharedCheck_4752_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4742_);
                            leanh::lean_dec(v___x_4741_);
                            v___x_4744_ = leanh::lean_box(0);
                            v_isShared_4745_ = v_isSharedCheck_4752_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4732_);
                        leanh::lean_dec(v_fst_4729_);
                        v_a_4753_ = leanh::lean_ctor_get(v___x_4741_, 0);
                        v_isSharedCheck_4760_ =
                            (!leanh::lean_is_exclusive(v___x_4741_)) as u8;
                        if v_isSharedCheck_4760_ == 0 {
                            v___x_4755_ = v___x_4741_;
                            v_isShared_4756_ = v_isSharedCheck_4760_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4753_);
                            leanh::lean_dec(v___x_4741_);
                            v___x_4755_ = leanh::lean_box(0);
                            v_isShared_4756_ = v_isSharedCheck_4760_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_4728_ == 0 {
                    leanh::lean_ctor_set(v___x_4727_, 0, v___x_4736_);
                    v___x_4738_ = v___x_4727_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v___x_4736_);
                    v___x_4738_ = v_reuseFailAlloc_4739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4738_;
            }
            7 => {
                if v_isShared_4733_ == 0 {
                    leanh::lean_ctor_set(v___x_4732_, 1, v_a_4742_);
                    v___x_4747_ = v___x_4732_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4751_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_fst_4729_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4751_, 1, v_a_4742_);
                    v___x_4747_ = v_reuseFailAlloc_4751_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4745_ == 0 {
                    leanh::lean_ctor_set(v___x_4744_, 0, v___x_4747_);
                    v___x_4749_ = v___x_4744_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v___x_4747_);
                    v___x_4749_ = v_reuseFailAlloc_4750_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4749_;
            }
            10 => {
                if v_isShared_4756_ == 0 {
                    v___x_4758_ = v___x_4755_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
                    v___x_4758_ = v_reuseFailAlloc_4759_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4758_;
            }
            12 => {
                if v_isShared_4766_ == 0 {
                    v___x_4768_ = v___x_4765_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
                    v___x_4768_ = v_reuseFailAlloc_4769_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg___boxed(
    mut v_d_4773_: *mut leanh::LeanObject,
    mut v_e_4774_: *mut leanh::LeanObject,
    mut v_a_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
    mut v_a_4777_: *mut leanh::LeanObject,
    mut v_a_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4780_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(
        v_d_4773_, v_e_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_,
    );
    leanh::lean_dec(v_a_4778_);
    leanh::lean_dec_ref(v_a_4777_);
    leanh::lean_dec(v_a_4776_);
    leanh::lean_dec_ref(v_a_4775_);
    leanh::lean_dec_ref(v_d_4773_);
    return v_res_4780_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(
    mut v_00_u03b1_4781_: *mut leanh::LeanObject,
    mut v_d_4782_: *mut leanh::LeanObject,
    mut v_e_4783_: *mut leanh::LeanObject,
    mut v_a_4784_: *mut leanh::LeanObject,
    mut v_a_4785_: *mut leanh::LeanObject,
    mut v_a_4786_: *mut leanh::LeanObject,
    mut v_a_4787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4789_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(
        v_d_4782_, v_e_4783_, v_a_4784_, v_a_4785_, v_a_4786_, v_a_4787_,
    );
    return v___x_4789_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___boxed(
    mut v_00_u03b1_4790_: *mut leanh::LeanObject,
    mut v_d_4791_: *mut leanh::LeanObject,
    mut v_e_4792_: *mut leanh::LeanObject,
    mut v_a_4793_: *mut leanh::LeanObject,
    mut v_a_4794_: *mut leanh::LeanObject,
    mut v_a_4795_: *mut leanh::LeanObject,
    mut v_a_4796_: *mut leanh::LeanObject,
    mut v_a_4797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4798_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore(
        v_00_u03b1_4790_,
        v_d_4791_,
        v_e_4792_,
        v_a_4793_,
        v_a_4794_,
        v_a_4795_,
        v_a_4796_,
    );
    leanh::lean_dec(v_a_4796_);
    leanh::lean_dec_ref(v_a_4795_);
    leanh::lean_dec(v_a_4794_);
    leanh::lean_dec_ref(v_a_4793_);
    leanh::lean_dec_ref(v_d_4791_);
    return v_res_4798_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatch___redArg(
    mut v_d_4799_: *mut leanh::LeanObject,
    mut v_e_4800_: *mut leanh::LeanObject,
    mut v_a_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
    mut v_a_4803_: *mut leanh::LeanObject,
    mut v_a_4804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v_snd_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_a_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4806_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_4799_, v_e_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
                if leanh::lean_obj_tag(v___x_4806_) == 0 {
                    v_a_4807_ = leanh::lean_ctor_get(v___x_4806_, 0);
                    v_isSharedCheck_4815_ = (!leanh::lean_is_exclusive(v___x_4806_)) as u8;
                    if v_isSharedCheck_4815_ == 0 {
                        v___x_4809_ = v___x_4806_;
                        v_isShared_4810_ = v_isSharedCheck_4815_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4807_);
                        leanh::lean_dec(v___x_4806_);
                        v___x_4809_ = leanh::lean_box(0);
                        v_isShared_4810_ = v_isSharedCheck_4815_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4816_ = leanh::lean_ctor_get(v___x_4806_, 0);
                    v_isSharedCheck_4823_ = (!leanh::lean_is_exclusive(v___x_4806_)) as u8;
                    if v_isSharedCheck_4823_ == 0 {
                        v___x_4818_ = v___x_4806_;
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4816_);
                        leanh::lean_dec(v___x_4806_);
                        v___x_4818_ = leanh::lean_box(0);
                        v_isShared_4819_ = v_isSharedCheck_4823_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4811_ = leanh::lean_ctor_get(v_a_4807_, 1);
                leanh::lean_inc(v_snd_4811_);
                leanh::lean_dec(v_a_4807_);
                if v_isShared_4810_ == 0 {
                    leanh::lean_ctor_set(v___x_4809_, 0, v_snd_4811_);
                    v___x_4813_ = v___x_4809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_snd_4811_);
                    v___x_4813_ = v_reuseFailAlloc_4814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4813_;
            }
            3 => {
                if v_isShared_4819_ == 0 {
                    v___x_4821_ = v___x_4818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
                    v___x_4821_ = v_reuseFailAlloc_4822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatch___redArg___boxed(
    mut v_d_4824_: *mut leanh::LeanObject,
    mut v_e_4825_: *mut leanh::LeanObject,
    mut v_a_4826_: *mut leanh::LeanObject,
    mut v_a_4827_: *mut leanh::LeanObject,
    mut v_a_4828_: *mut leanh::LeanObject,
    mut v_a_4829_: *mut leanh::LeanObject,
    mut v_a_4830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_Lean_Meta_DiscrTree_getMatch___redArg(
        v_d_4824_, v_e_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_,
    );
    leanh::lean_dec(v_a_4829_);
    leanh::lean_dec_ref(v_a_4828_);
    leanh::lean_dec(v_a_4827_);
    leanh::lean_dec_ref(v_a_4826_);
    leanh::lean_dec_ref(v_d_4824_);
    return v_res_4831_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatch(
    mut v_00_u03b1_4832_: *mut leanh::LeanObject,
    mut v_d_4833_: *mut leanh::LeanObject,
    mut v_e_4834_: *mut leanh::LeanObject,
    mut v_a_4835_: *mut leanh::LeanObject,
    mut v_a_4836_: *mut leanh::LeanObject,
    mut v_a_4837_: *mut leanh::LeanObject,
    mut v_a_4838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4840_ = l_Lean_Meta_DiscrTree_getMatch___redArg(
        v_d_4833_, v_e_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_,
    );
    return v___x_4840_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatch___boxed(
    mut v_00_u03b1_4841_: *mut leanh::LeanObject,
    mut v_d_4842_: *mut leanh::LeanObject,
    mut v_e_4843_: *mut leanh::LeanObject,
    mut v_a_4844_: *mut leanh::LeanObject,
    mut v_a_4845_: *mut leanh::LeanObject,
    mut v_a_4846_: *mut leanh::LeanObject,
    mut v_a_4847_: *mut leanh::LeanObject,
    mut v_a_4848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4849_ = l_Lean_Meta_DiscrTree_getMatch(
        v_00_u03b1_4841_,
        v_d_4842_,
        v_e_4843_,
        v_a_4844_,
        v_a_4845_,
        v_a_4846_,
        v_a_4847_,
    );
    leanh::lean_dec(v_a_4847_);
    leanh::lean_dec_ref(v_a_4846_);
    leanh::lean_dec(v_a_4845_);
    leanh::lean_dec_ref(v_a_4844_);
    leanh::lean_dec_ref(v_d_4842_);
    return v_res_4849_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(
    mut v_d_4850_: *mut leanh::LeanObject,
    mut v_k_4851_: *mut leanh::LeanObject,
    mut v_a_4852_: *mut leanh::LeanObject,
    mut v_a_4853_: *mut leanh::LeanObject,
    mut v_a_4854_: *mut leanh::LeanObject,
    mut v_a_4855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4858_: u8 = 0;
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4871_: u8 = 0;
    let mut v___x_4872_: u8 = 0;
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4877_: u8 = 0;
    let mut v_unused_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4883_: u8 = 0;
    let mut v_zero_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4885_: u8 = 0;
    let mut v_one_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4891_: u8 = 0;
    let mut v_a_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4896_: u8 = 0;
    let mut v_zero_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4898_: u8 = 0;
    let mut v_one_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4904_: u8 = 0;
    let mut v_a_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4910_: u8 = 0;
    let mut v_zero_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4912_: u8 = 0;
    let mut v_one_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_k_4851_) {
                4 => {
                    v_a_4879_ = leanh::lean_ctor_get(v_k_4851_, 0);
                    v_a_4880_ = leanh::lean_ctor_get(v_k_4851_, 1);
                    v_isSharedCheck_4891_ = (!leanh::lean_is_exclusive(v_k_4851_)) as u8;
                    if v_isSharedCheck_4891_ == 0 {
                        v___x_4882_ = v_k_4851_;
                        v_isShared_4883_ = v_isSharedCheck_4891_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4880_);
                        leanh::lean_inc(v_a_4879_);
                        leanh::lean_dec(v_k_4851_);
                        v___x_4882_ = leanh::lean_box(0);
                        v_isShared_4883_ = v_isSharedCheck_4891_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_a_4892_ = leanh::lean_ctor_get(v_k_4851_, 0);
                    v_a_4893_ = leanh::lean_ctor_get(v_k_4851_, 1);
                    v_isSharedCheck_4904_ = (!leanh::lean_is_exclusive(v_k_4851_)) as u8;
                    if v_isSharedCheck_4904_ == 0 {
                        v___x_4895_ = v_k_4851_;
                        v_isShared_4896_ = v_isSharedCheck_4904_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4893_);
                        leanh::lean_inc(v_a_4892_);
                        leanh::lean_dec(v_k_4851_);
                        v___x_4895_ = leanh::lean_box(0);
                        v_isShared_4896_ = v_isSharedCheck_4904_;
                        state = 7;
                        continue;
                    }
                }
                6 => {
                    v_a_4905_ = leanh::lean_ctor_get(v_k_4851_, 0);
                    v_a_4906_ = leanh::lean_ctor_get(v_k_4851_, 1);
                    v_a_4907_ = leanh::lean_ctor_get(v_k_4851_, 2);
                    v_isSharedCheck_4918_ = (!leanh::lean_is_exclusive(v_k_4851_)) as u8;
                    if v_isSharedCheck_4918_ == 0 {
                        v___x_4909_ = v_k_4851_;
                        v_isShared_4910_ = v_isSharedCheck_4918_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4907_);
                        leanh::lean_inc(v_a_4906_);
                        leanh::lean_inc(v_a_4905_);
                        leanh::lean_dec(v_k_4851_);
                        v___x_4909_ = leanh::lean_box(0);
                        v_isShared_4910_ = v_isSharedCheck_4918_;
                        state = 9;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_k_4851_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_4858_ = 0;
                v___x_4859_ = leanh::lean_box((v___x_4858_) as usize);
                v___x_4860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4860_, 0, v___x_4859_);
                return v___x_4860_;
            }
            2 => {
                v___x_4867_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_4850_, v_k_4862_);
                if leanh::lean_obj_tag(v___x_4867_) == 0 {
                    v_k_4851_ = v_k_4862_;
                    v_a_4852_ = v___y_4863_;
                    v_a_4853_ = v___y_4864_;
                    v_a_4854_ = v___y_4865_;
                    v_a_4855_ = v___y_4866_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_k_4862_);
                    v_isSharedCheck_4877_ = (!leanh::lean_is_exclusive(v___x_4867_)) as u8;
                    if v_isSharedCheck_4877_ == 0 {
                        v_unused_4878_ = leanh::lean_ctor_get(v___x_4867_, 0);
                        leanh::lean_dec(v_unused_4878_);
                        v___x_4870_ = v___x_4867_;
                        v_isShared_4871_ = v_isSharedCheck_4877_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4867_);
                        v___x_4870_ = leanh::lean_box(0);
                        v_isShared_4871_ = v_isSharedCheck_4877_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4872_ = 1;
                v___x_4873_ = leanh::lean_box((v___x_4872_) as usize);
                if v_isShared_4871_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4870_, 0);
                    leanh::lean_ctor_set(v___x_4870_, 0, v___x_4873_);
                    v___x_4875_ = v___x_4870_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
                    v___x_4875_ = v_reuseFailAlloc_4876_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4875_;
            }
            5 => {
                v_zero_4884_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4885_ = lean_nat_dec_eq(v_a_4880_, v_zero_4884_);
                if v_isZero_4885_ == 0 {
                    v_one_4886_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4887_ = lean_nat_sub(v_a_4880_, v_one_4886_);
                    leanh::lean_dec(v_a_4880_);
                    if v_isShared_4883_ == 0 {
                        leanh::lean_ctor_set(v___x_4882_, 1, v_n_4887_);
                        v___x_4889_ = v___x_4882_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4890_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4879_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 1, v_n_4887_);
                        v___x_4889_ = v_reuseFailAlloc_4890_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4882_);
                    leanh::lean_dec(v_a_4880_);
                    leanh::lean_dec(v_a_4879_);
                    state = 1;
                    continue;
                }
            }
            6 => {
                v_k_4862_ = v___x_4889_;
                v___y_4863_ = v_a_4852_;
                v___y_4864_ = v_a_4853_;
                v___y_4865_ = v_a_4854_;
                v___y_4866_ = v_a_4855_;
                state = 2;
                continue;
            }
            7 => {
                v_zero_4897_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4898_ = lean_nat_dec_eq(v_a_4893_, v_zero_4897_);
                if v_isZero_4898_ == 0 {
                    v_one_4899_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4900_ = lean_nat_sub(v_a_4893_, v_one_4899_);
                    leanh::lean_dec(v_a_4893_);
                    if v_isShared_4896_ == 0 {
                        leanh::lean_ctor_set(v___x_4895_, 1, v_n_4900_);
                        v___x_4902_ = v___x_4895_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4903_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4892_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4903_, 1, v_n_4900_);
                        v___x_4902_ = v_reuseFailAlloc_4903_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4895_);
                    leanh::lean_dec(v_a_4893_);
                    leanh::lean_dec(v_a_4892_);
                    state = 1;
                    continue;
                }
            }
            8 => {
                v_k_4862_ = v___x_4902_;
                v___y_4863_ = v_a_4852_;
                v___y_4864_ = v_a_4853_;
                v___y_4865_ = v_a_4854_;
                v___y_4866_ = v_a_4855_;
                state = 2;
                continue;
            }
            9 => {
                v_zero_4911_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4912_ = lean_nat_dec_eq(v_a_4907_, v_zero_4911_);
                if v_isZero_4912_ == 0 {
                    v_one_4913_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4914_ = lean_nat_sub(v_a_4907_, v_one_4913_);
                    leanh::lean_dec(v_a_4907_);
                    if v_isShared_4910_ == 0 {
                        leanh::lean_ctor_set(v___x_4909_, 2, v_n_4914_);
                        v___x_4916_ = v___x_4909_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4917_ = leanh::lean_alloc_ctor(6, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4905_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4917_, 1, v_a_4906_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4917_, 2, v_n_4914_);
                        v___x_4916_ = v_reuseFailAlloc_4917_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4909_);
                    leanh::lean_dec(v_a_4907_);
                    leanh::lean_dec(v_a_4906_);
                    leanh::lean_dec(v_a_4905_);
                    state = 1;
                    continue;
                }
            }
            10 => {
                v_k_4862_ = v___x_4916_;
                v___y_4863_ = v_a_4852_;
                v___y_4864_ = v_a_4853_;
                v___y_4865_ = v_a_4854_;
                v___y_4866_ = v_a_4855_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg___boxed(
    mut v_d_4919_: *mut leanh::LeanObject,
    mut v_k_4920_: *mut leanh::LeanObject,
    mut v_a_4921_: *mut leanh::LeanObject,
    mut v_a_4922_: *mut leanh::LeanObject,
    mut v_a_4923_: *mut leanh::LeanObject,
    mut v_a_4924_: *mut leanh::LeanObject,
    mut v_a_4925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4926_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_4919_, v_k_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_);
    leanh::lean_dec(v_a_4924_);
    leanh::lean_dec_ref(v_a_4923_);
    leanh::lean_dec(v_a_4922_);
    leanh::lean_dec_ref(v_a_4921_);
    leanh::lean_dec_ref(v_d_4919_);
    return v_res_4926_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(
    mut v_00_u03b1_4927_: *mut leanh::LeanObject,
    mut v_d_4928_: *mut leanh::LeanObject,
    mut v_k_4929_: *mut leanh::LeanObject,
    mut v_a_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4935_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_4928_, v_k_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
    return v___x_4935_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___boxed(
    mut v_00_u03b1_4936_: *mut leanh::LeanObject,
    mut v_d_4937_: *mut leanh::LeanObject,
    mut v_k_4938_: *mut leanh::LeanObject,
    mut v_a_4939_: *mut leanh::LeanObject,
    mut v_a_4940_: *mut leanh::LeanObject,
    mut v_a_4941_: *mut leanh::LeanObject,
    mut v_a_4942_: *mut leanh::LeanObject,
    mut v_a_4943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4944_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix(v_00_u03b1_4936_, v_d_4937_, v_k_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
    leanh::lean_dec(v_a_4942_);
    leanh::lean_dec_ref(v_a_4941_);
    leanh::lean_dec(v_a_4940_);
    leanh::lean_dec_ref(v_a_4939_);
    leanh::lean_dec_ref(v_d_4937_);
    return v_res_4944_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(
    mut v_numExtra_4945_: *mut leanh::LeanObject,
    mut v_sz_4946_: usize,
    mut v_i_4947_: usize,
    mut v_bs_4948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4949_: u8 = 0;
    let mut v_v_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: usize = 0;
    let mut v___x_4955_: usize = 0;
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4949_ = lean_usize_dec_lt(v_i_4947_, v_sz_4946_);
                if v___x_4949_ == 0 {
                    leanh::lean_dec(v_numExtra_4945_);
                    return v_bs_4948_;
                } else {
                    v_v_4950_ = lean_array_uget(v_bs_4948_, v_i_4947_);
                    v___x_4951_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4952_ = lean_array_uset(v_bs_4948_, v_i_4947_, v___x_4951_);
                    leanh::lean_inc(v_numExtra_4945_);
                    v___x_4953_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4953_, 0, v_v_4950_);
                    leanh::lean_ctor_set(v___x_4953_, 1, v_numExtra_4945_);
                    v___x_4954_ = 1usize;
                    v___x_4955_ = lean_usize_add(v_i_4947_, v___x_4954_);
                    v___x_4956_ = lean_array_uset(v_bs_x27_4952_, v_i_4947_, v___x_4953_);
                    v_i_4947_ = v___x_4955_;
                    v_bs_4948_ = v___x_4956_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg___boxed(
    mut v_numExtra_4958_: *mut leanh::LeanObject,
    mut v_sz_4959_: *mut leanh::LeanObject,
    mut v_i_4960_: *mut leanh::LeanObject,
    mut v_bs_4961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4962_: usize = 0;
    let mut v_i_boxed_4963_: usize = 0;
    let mut v_res_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4962_ = leanh::lean_unbox_usize(v_sz_4959_);
    leanh::lean_dec(v_sz_4959_);
    v_i_boxed_4963_ = leanh::lean_unbox_usize(v_i_4960_);
    leanh::lean_dec(v_i_4960_);
    v_res_4964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_4958_, v_sz_boxed_4962_, v_i_boxed_4963_, v_bs_4961_);
    return v_res_4964_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(
    mut v_d_4965_: *mut leanh::LeanObject,
    mut v_e_4966_: *mut leanh::LeanObject,
    mut v_numExtra_4967_: *mut leanh::LeanObject,
    mut v_result_4968_: *mut leanh::LeanObject,
    mut v_a_4969_: *mut leanh::LeanObject,
    mut v_a_4970_: *mut leanh::LeanObject,
    mut v_a_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v_snd_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4980_: usize = 0;
    let mut v___x_4981_: usize = 0;
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut v_a_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4996_: u8 = 0;
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_4966_);
                v___x_4974_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_4965_, v_e_4966_, v_a_4969_, v_a_4970_, v_a_4971_, v_a_4972_);
                if leanh::lean_obj_tag(v___x_4974_) == 0 {
                    v_a_4975_ = leanh::lean_ctor_get(v___x_4974_, 0);
                    v_isSharedCheck_4992_ = (!leanh::lean_is_exclusive(v___x_4974_)) as u8;
                    if v_isSharedCheck_4992_ == 0 {
                        v___x_4977_ = v___x_4974_;
                        v_isShared_4978_ = v_isSharedCheck_4992_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4975_);
                        leanh::lean_dec(v___x_4974_);
                        v___x_4977_ = leanh::lean_box(0);
                        v_isShared_4978_ = v_isSharedCheck_4992_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_result_4968_);
                    leanh::lean_dec(v_numExtra_4967_);
                    leanh::lean_dec_ref(v_e_4966_);
                    v_a_4993_ = leanh::lean_ctor_get(v___x_4974_, 0);
                    v_isSharedCheck_5000_ = (!leanh::lean_is_exclusive(v___x_4974_)) as u8;
                    if v_isSharedCheck_5000_ == 0 {
                        v___x_4995_ = v___x_4974_;
                        v_isShared_4996_ = v_isSharedCheck_5000_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4993_);
                        leanh::lean_dec(v___x_4974_);
                        v___x_4995_ = leanh::lean_box(0);
                        v_isShared_4996_ = v_isSharedCheck_5000_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4979_ = leanh::lean_ctor_get(v_a_4975_, 1);
                leanh::lean_inc(v_snd_4979_);
                leanh::lean_dec(v_a_4975_);
                v_sz_4980_ = lean_array_size(v_snd_4979_);
                v___x_4981_ = 0usize;
                leanh::lean_inc(v_numExtra_4967_);
                v___x_4982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_4967_, v_sz_4980_, v___x_4981_, v_snd_4979_);
                v___x_4983_ = l_Array_append___redArg(v_result_4968_, v___x_4982_);
                leanh::lean_dec_ref(v___x_4982_);
                v___x_4984_ = l_Lean_Expr_isApp(v_e_4966_);
                if v___x_4984_ == 0 {
                    leanh::lean_dec(v_numExtra_4967_);
                    leanh::lean_dec_ref(v_e_4966_);
                    if v_isShared_4978_ == 0 {
                        leanh::lean_ctor_set(v___x_4977_, 0, v___x_4983_);
                        v___x_4986_ = v___x_4977_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4983_);
                        v___x_4986_ = v_reuseFailAlloc_4987_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4977_);
                    v___x_4988_ = l_Lean_Expr_appFn_x21(v_e_4966_);
                    leanh::lean_dec_ref(v_e_4966_);
                    v___x_4989_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4990_ = lean_nat_add(v_numExtra_4967_, v___x_4989_);
                    leanh::lean_dec(v_numExtra_4967_);
                    v_e_4966_ = v___x_4988_;
                    v_numExtra_4967_ = v___x_4990_;
                    v_result_4968_ = v___x_4983_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_4986_;
            }
            3 => {
                if v_isShared_4996_ == 0 {
                    v___x_4998_ = v___x_4995_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4999_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
                    v___x_4998_ = v_reuseFailAlloc_4999_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg___boxed(
    mut v_d_5001_: *mut leanh::LeanObject,
    mut v_e_5002_: *mut leanh::LeanObject,
    mut v_numExtra_5003_: *mut leanh::LeanObject,
    mut v_result_5004_: *mut leanh::LeanObject,
    mut v_a_5005_: *mut leanh::LeanObject,
    mut v_a_5006_: *mut leanh::LeanObject,
    mut v_a_5007_: *mut leanh::LeanObject,
    mut v_a_5008_: *mut leanh::LeanObject,
    mut v_a_5009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5010_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(
            v_d_5001_,
            v_e_5002_,
            v_numExtra_5003_,
            v_result_5004_,
            v_a_5005_,
            v_a_5006_,
            v_a_5007_,
            v_a_5008_,
        );
    leanh::lean_dec(v_a_5008_);
    leanh::lean_dec_ref(v_a_5007_);
    leanh::lean_dec(v_a_5006_);
    leanh::lean_dec_ref(v_a_5005_);
    leanh::lean_dec_ref(v_d_5001_);
    return v_res_5010_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(
    mut v_00_u03b1_5011_: *mut leanh::LeanObject,
    mut v_d_5012_: *mut leanh::LeanObject,
    mut v_e_5013_: *mut leanh::LeanObject,
    mut v_numExtra_5014_: *mut leanh::LeanObject,
    mut v_result_5015_: *mut leanh::LeanObject,
    mut v_a_5016_: *mut leanh::LeanObject,
    mut v_a_5017_: *mut leanh::LeanObject,
    mut v_a_5018_: *mut leanh::LeanObject,
    mut v_a_5019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5021_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(
            v_d_5012_,
            v_e_5013_,
            v_numExtra_5014_,
            v_result_5015_,
            v_a_5016_,
            v_a_5017_,
            v_a_5018_,
            v_a_5019_,
        );
    return v___x_5021_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___boxed(
    mut v_00_u03b1_5022_: *mut leanh::LeanObject,
    mut v_d_5023_: *mut leanh::LeanObject,
    mut v_e_5024_: *mut leanh::LeanObject,
    mut v_numExtra_5025_: *mut leanh::LeanObject,
    mut v_result_5026_: *mut leanh::LeanObject,
    mut v_a_5027_: *mut leanh::LeanObject,
    mut v_a_5028_: *mut leanh::LeanObject,
    mut v_a_5029_: *mut leanh::LeanObject,
    mut v_a_5030_: *mut leanh::LeanObject,
    mut v_a_5031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5032_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go(
        v_00_u03b1_5022_,
        v_d_5023_,
        v_e_5024_,
        v_numExtra_5025_,
        v_result_5026_,
        v_a_5027_,
        v_a_5028_,
        v_a_5029_,
        v_a_5030_,
    );
    leanh::lean_dec(v_a_5030_);
    leanh::lean_dec_ref(v_a_5029_);
    leanh::lean_dec(v_a_5028_);
    leanh::lean_dec_ref(v_a_5027_);
    leanh::lean_dec_ref(v_d_5023_);
    return v_res_5032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(
    mut v_00_u03b1_5033_: *mut leanh::LeanObject,
    mut v_numExtra_5034_: *mut leanh::LeanObject,
    mut v_sz_5035_: usize,
    mut v_i_5036_: usize,
    mut v_bs_5037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___redArg(v_numExtra_5034_, v_sz_5035_, v_i_5036_, v_bs_5037_);
    return v___x_5038_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0___boxed(
    mut v_00_u03b1_5039_: *mut leanh::LeanObject,
    mut v_numExtra_5040_: *mut leanh::LeanObject,
    mut v_sz_5041_: *mut leanh::LeanObject,
    mut v_i_5042_: *mut leanh::LeanObject,
    mut v_bs_5043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5044_: usize = 0;
    let mut v_i_boxed_5045_: usize = 0;
    let mut v_res_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5044_ = leanh::lean_unbox_usize(v_sz_5041_);
    leanh::lean_dec(v_sz_5041_);
    v_i_boxed_5045_ = leanh::lean_unbox_usize(v_i_5042_);
    leanh::lean_dec(v_i_5042_);
    v_res_5046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go_spec__0(v_00_u03b1_5039_, v_numExtra_5040_, v_sz_boxed_5044_, v_i_boxed_5045_, v_bs_5043_);
    return v_res_5046_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(
    mut v_sz_5047_: usize,
    mut v_i_5048_: usize,
    mut v_bs_5049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5050_: u8 = 0;
    let mut v_v_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: usize = 0;
    let mut v___x_5056_: usize = 0;
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5050_ = lean_usize_dec_lt(v_i_5048_, v_sz_5047_);
                if v___x_5050_ == 0 {
                    return v_bs_5049_;
                } else {
                    v_v_5051_ = lean_array_uget(v_bs_5049_, v_i_5048_);
                    v___x_5052_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5053_ = lean_array_uset(v_bs_5049_, v_i_5048_, v___x_5052_);
                    v___x_5054_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5054_, 0, v_v_5051_);
                    leanh::lean_ctor_set(v___x_5054_, 1, v___x_5052_);
                    v___x_5055_ = 1usize;
                    v___x_5056_ = lean_usize_add(v_i_5048_, v___x_5055_);
                    v___x_5057_ = lean_array_uset(v_bs_x27_5053_, v_i_5048_, v___x_5054_);
                    v_i_5048_ = v___x_5056_;
                    v_bs_5049_ = v___x_5057_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg___boxed(
    mut v_sz_5059_: *mut leanh::LeanObject,
    mut v_i_5060_: *mut leanh::LeanObject,
    mut v_bs_5061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5062_: usize = 0;
    let mut v_i_boxed_5063_: usize = 0;
    let mut v_res_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5062_ = leanh::lean_unbox_usize(v_sz_5059_);
    leanh::lean_dec(v_sz_5059_);
    v_i_boxed_5063_ = leanh::lean_unbox_usize(v_i_5060_);
    leanh::lean_dec(v_i_5060_);
    v_res_5064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_boxed_5062_, v_i_boxed_5063_, v_bs_5061_);
    return v_res_5064_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(
    mut v_d_5065_: *mut leanh::LeanObject,
    mut v_e_5066_: *mut leanh::LeanObject,
    mut v_a_5067_: *mut leanh::LeanObject,
    mut v_a_5068_: *mut leanh::LeanObject,
    mut v_a_5069_: *mut leanh::LeanObject,
    mut v_a_5070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5076_: u8 = 0;
    let mut v_fst_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5079_: usize = 0;
    let mut v___x_5080_: usize = 0;
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: u8 = 0;
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5091_: u8 = 0;
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut v_a_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5106_: u8 = 0;
    let mut v_isSharedCheck_5107_: u8 = 0;
    let mut v_a_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5111_: u8 = 0;
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_5066_);
                v___x_5072_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchCore___redArg(v_d_5065_, v_e_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
                if leanh::lean_obj_tag(v___x_5072_) == 0 {
                    v_a_5073_ = leanh::lean_ctor_get(v___x_5072_, 0);
                    v_isSharedCheck_5107_ = (!leanh::lean_is_exclusive(v___x_5072_)) as u8;
                    if v_isSharedCheck_5107_ == 0 {
                        v___x_5075_ = v___x_5072_;
                        v_isShared_5076_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5073_);
                        leanh::lean_dec(v___x_5072_);
                        v___x_5075_ = leanh::lean_box(0);
                        v_isShared_5076_ = v_isSharedCheck_5107_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5066_);
                    v_a_5108_ = leanh::lean_ctor_get(v___x_5072_, 0);
                    v_isSharedCheck_5115_ = (!leanh::lean_is_exclusive(v___x_5072_)) as u8;
                    if v_isSharedCheck_5115_ == 0 {
                        v___x_5110_ = v___x_5072_;
                        v_isShared_5111_ = v_isSharedCheck_5115_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5108_);
                        leanh::lean_dec(v___x_5072_);
                        v___x_5110_ = leanh::lean_box(0);
                        v_isShared_5111_ = v_isSharedCheck_5115_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5077_ = leanh::lean_ctor_get(v_a_5073_, 0);
                leanh::lean_inc(v_fst_5077_);
                v_snd_5078_ = leanh::lean_ctor_get(v_a_5073_, 1);
                leanh::lean_inc(v_snd_5078_);
                leanh::lean_dec(v_a_5073_);
                v_sz_5079_ = lean_array_size(v_snd_5078_);
                v___x_5080_ = 0usize;
                v___x_5081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_5079_, v___x_5080_, v_snd_5078_);
                v___x_5082_ = l_Lean_Expr_isApp(v_e_5066_);
                if v___x_5082_ == 0 {
                    leanh::lean_dec(v_fst_5077_);
                    leanh::lean_dec_ref(v_e_5066_);
                    if v_isShared_5076_ == 0 {
                        leanh::lean_ctor_set(v___x_5075_, 0, v___x_5081_);
                        v___x_5084_ = v___x_5075_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5081_);
                        v___x_5084_ = v_reuseFailAlloc_5085_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5075_);
                    v___x_5086_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_mayMatchPrefix___redArg(v_d_5065_, v_fst_5077_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
                    if leanh::lean_obj_tag(v___x_5086_) == 0 {
                        v_a_5087_ = leanh::lean_ctor_get(v___x_5086_, 0);
                        v_isSharedCheck_5098_ =
                            (!leanh::lean_is_exclusive(v___x_5086_)) as u8;
                        if v_isSharedCheck_5098_ == 0 {
                            v___x_5089_ = v___x_5086_;
                            v_isShared_5090_ = v_isSharedCheck_5098_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5087_);
                            leanh::lean_dec(v___x_5086_);
                            v___x_5089_ = leanh::lean_box(0);
                            v_isShared_5090_ = v_isSharedCheck_5098_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5081_);
                        leanh::lean_dec_ref(v_e_5066_);
                        v_a_5099_ = leanh::lean_ctor_get(v___x_5086_, 0);
                        v_isSharedCheck_5106_ =
                            (!leanh::lean_is_exclusive(v___x_5086_)) as u8;
                        if v_isSharedCheck_5106_ == 0 {
                            v___x_5101_ = v___x_5086_;
                            v_isShared_5102_ = v_isSharedCheck_5106_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5099_);
                            leanh::lean_dec(v___x_5086_);
                            v___x_5101_ = leanh::lean_box(0);
                            v_isShared_5102_ = v_isSharedCheck_5106_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5084_;
            }
            3 => {
                v___x_5091_ = (leanh::lean_unbox(v_a_5087_) as u8);
                leanh::lean_dec(v_a_5087_);
                if v___x_5091_ == 0 {
                    leanh::lean_dec_ref(v_e_5066_);
                    if v_isShared_5090_ == 0 {
                        leanh::lean_ctor_set(v___x_5089_, 0, v___x_5081_);
                        v___x_5093_ = v___x_5089_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_5081_);
                        v___x_5093_ = v_reuseFailAlloc_5094_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5089_);
                    v___x_5095_ = l_Lean_Expr_appFn_x21(v_e_5066_);
                    leanh::lean_dec_ref(v_e_5066_);
                    v___x_5096_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5097_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchWithExtra_go___redArg(v_d_5065_, v___x_5095_, v___x_5096_, v___x_5081_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
                    return v___x_5097_;
                }
            }
            4 => {
                return v___x_5093_;
            }
            5 => {
                if v_isShared_5102_ == 0 {
                    v___x_5104_ = v___x_5101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
                    v___x_5104_ = v_reuseFailAlloc_5105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5104_;
            }
            7 => {
                if v_isShared_5111_ == 0 {
                    v___x_5113_ = v___x_5110_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_a_5108_);
                    v___x_5113_ = v_reuseFailAlloc_5114_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg___boxed(
    mut v_d_5116_: *mut leanh::LeanObject,
    mut v_e_5117_: *mut leanh::LeanObject,
    mut v_a_5118_: *mut leanh::LeanObject,
    mut v_a_5119_: *mut leanh::LeanObject,
    mut v_a_5120_: *mut leanh::LeanObject,
    mut v_a_5121_: *mut leanh::LeanObject,
    mut v_a_5122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5123_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(
        v_d_5116_, v_e_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_,
    );
    leanh::lean_dec(v_a_5121_);
    leanh::lean_dec_ref(v_a_5120_);
    leanh::lean_dec(v_a_5119_);
    leanh::lean_dec_ref(v_a_5118_);
    leanh::lean_dec_ref(v_d_5116_);
    return v_res_5123_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchWithExtra(
    mut v_00_u03b1_5124_: *mut leanh::LeanObject,
    mut v_d_5125_: *mut leanh::LeanObject,
    mut v_e_5126_: *mut leanh::LeanObject,
    mut v_a_5127_: *mut leanh::LeanObject,
    mut v_a_5128_: *mut leanh::LeanObject,
    mut v_a_5129_: *mut leanh::LeanObject,
    mut v_a_5130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5132_ = l_Lean_Meta_DiscrTree_getMatchWithExtra___redArg(
        v_d_5125_, v_e_5126_, v_a_5127_, v_a_5128_, v_a_5129_, v_a_5130_,
    );
    return v___x_5132_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchWithExtra___boxed(
    mut v_00_u03b1_5133_: *mut leanh::LeanObject,
    mut v_d_5134_: *mut leanh::LeanObject,
    mut v_e_5135_: *mut leanh::LeanObject,
    mut v_a_5136_: *mut leanh::LeanObject,
    mut v_a_5137_: *mut leanh::LeanObject,
    mut v_a_5138_: *mut leanh::LeanObject,
    mut v_a_5139_: *mut leanh::LeanObject,
    mut v_a_5140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5141_ = l_Lean_Meta_DiscrTree_getMatchWithExtra(
        v_00_u03b1_5133_,
        v_d_5134_,
        v_e_5135_,
        v_a_5136_,
        v_a_5137_,
        v_a_5138_,
        v_a_5139_,
    );
    leanh::lean_dec(v_a_5139_);
    leanh::lean_dec_ref(v_a_5138_);
    leanh::lean_dec(v_a_5137_);
    leanh::lean_dec_ref(v_a_5136_);
    leanh::lean_dec_ref(v_d_5134_);
    return v_res_5141_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(
    mut v_00_u03b1_5142_: *mut leanh::LeanObject,
    mut v_sz_5143_: usize,
    mut v_i_5144_: usize,
    mut v_bs_5145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5146_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___redArg(v_sz_5143_, v_i_5144_, v_bs_5145_);
    return v___x_5146_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0___boxed(
    mut v_00_u03b1_5147_: *mut leanh::LeanObject,
    mut v_sz_5148_: *mut leanh::LeanObject,
    mut v_i_5149_: *mut leanh::LeanObject,
    mut v_bs_5150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5151_: usize = 0;
    let mut v_i_boxed_5152_: usize = 0;
    let mut v_res_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5151_ = leanh::lean_unbox_usize(v_sz_5148_);
    leanh::lean_dec(v_sz_5148_);
    v_i_boxed_5152_ = leanh::lean_unbox_usize(v_i_5149_);
    leanh::lean_dec(v_i_5149_);
    v_res_5153_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_DiscrTree_getMatchWithExtra_spec__0(v_00_u03b1_5147_, v_sz_boxed_5151_, v_i_boxed_5152_, v_bs_5150_);
    return v_res_5153_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchKeyRootFor(
    mut v_e_5154_: *mut leanh::LeanObject,
    mut v_a_5155_: *mut leanh::LeanObject,
    mut v_a_5156_: *mut leanh::LeanObject,
    mut v_a_5157_: *mut leanh::LeanObject,
    mut v_a_5158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5160_: u8 = 0;
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut v_a_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5160_ = 1;
                v___x_5161_ = l_Lean_Meta_DiscrTree_reduceDT(
                    v_e_5154_,
                    v___x_5160_,
                    v_a_5155_,
                    v_a_5156_,
                    v_a_5157_,
                    v_a_5158_,
                );
                if leanh::lean_obj_tag(v___x_5161_) == 0 {
                    v_a_5162_ = leanh::lean_ctor_get(v___x_5161_, 0);
                    v_isSharedCheck_5186_ = (!leanh::lean_is_exclusive(v___x_5161_)) as u8;
                    if v_isSharedCheck_5186_ == 0 {
                        v___x_5164_ = v___x_5161_;
                        v_isShared_5165_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5162_);
                        leanh::lean_dec(v___x_5161_);
                        v___x_5164_ = leanh::lean_box(0);
                        v_isShared_5165_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5187_ = leanh::lean_ctor_get(v___x_5161_, 0);
                    v_isSharedCheck_5194_ = (!leanh::lean_is_exclusive(v___x_5161_)) as u8;
                    if v_isSharedCheck_5194_ == 0 {
                        v___x_5189_ = v___x_5161_;
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5187_);
                        leanh::lean_dec(v___x_5161_);
                        v___x_5189_ = leanh::lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5166_ = l_Lean_Expr_getAppNumArgs(v_a_5162_);
                v___x_5173_ = l_Lean_Expr_getAppFn(v_a_5162_);
                leanh::lean_dec(v_a_5162_);
                match leanh::lean_obj_tag(v___x_5173_) {
                    9 => {
                        v_a_5174_ = leanh::lean_ctor_get(v___x_5173_, 0);
                        leanh::lean_inc_ref(v_a_5174_);
                        leanh::lean_dec_ref_known(v___x_5173_, 1);
                        v___x_5175_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5175_, 0, v_a_5174_);
                        v___y_5168_ = v___x_5175_;
                        state = 2;
                        continue;
                    }
                    1 => {
                        v_fvarId_5176_ = leanh::lean_ctor_get(v___x_5173_, 0);
                        leanh::lean_inc(v_fvarId_5176_);
                        leanh::lean_dec_ref_known(v___x_5173_, 1);
                        leanh::lean_inc(v___x_5166_);
                        v___x_5177_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5177_, 0, v_fvarId_5176_);
                        leanh::lean_ctor_set(v___x_5177_, 1, v___x_5166_);
                        v___y_5168_ = v___x_5177_;
                        state = 2;
                        continue;
                    }
                    2 => {
                        leanh::lean_dec_ref_known(v___x_5173_, 1);
                        v___x_5178_ = leanh::lean_box(1);
                        v___y_5168_ = v___x_5178_;
                        state = 2;
                        continue;
                    }
                    11 => {
                        v_typeName_5179_ = leanh::lean_ctor_get(v___x_5173_, 0);
                        leanh::lean_inc(v_typeName_5179_);
                        v_idx_5180_ = leanh::lean_ctor_get(v___x_5173_, 1);
                        leanh::lean_inc(v_idx_5180_);
                        leanh::lean_dec_ref_known(v___x_5173_, 3);
                        leanh::lean_inc(v___x_5166_);
                        v___x_5181_ = leanh::lean_alloc_ctor(6, 3, (0) as u32);
                        leanh::lean_ctor_set(v___x_5181_, 0, v_typeName_5179_);
                        leanh::lean_ctor_set(v___x_5181_, 1, v_idx_5180_);
                        leanh::lean_ctor_set(v___x_5181_, 2, v___x_5166_);
                        v___y_5168_ = v___x_5181_;
                        state = 2;
                        continue;
                    }
                    7 => {
                        leanh::lean_dec_ref_known(v___x_5173_, 3);
                        v___x_5182_ = leanh::lean_box(5);
                        v___y_5168_ = v___x_5182_;
                        state = 2;
                        continue;
                    }
                    4 => {
                        v_declName_5183_ = leanh::lean_ctor_get(v___x_5173_, 0);
                        leanh::lean_inc(v_declName_5183_);
                        leanh::lean_dec_ref_known(v___x_5173_, 2);
                        leanh::lean_inc(v___x_5166_);
                        v___x_5184_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5184_, 0, v_declName_5183_);
                        leanh::lean_ctor_set(v___x_5184_, 1, v___x_5166_);
                        v___y_5168_ = v___x_5184_;
                        state = 2;
                        continue;
                    }
                    _ => {
                        leanh::lean_dec_ref(v___x_5173_);
                        v___x_5185_ = leanh::lean_box(1);
                        v___y_5168_ = v___x_5185_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5169_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5169_, 0, v___y_5168_);
                leanh::lean_ctor_set(v___x_5169_, 1, v___x_5166_);
                if v_isShared_5165_ == 0 {
                    leanh::lean_ctor_set(v___x_5164_, 0, v___x_5169_);
                    v___x_5171_ = v___x_5164_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5169_);
                    v___x_5171_ = v_reuseFailAlloc_5172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5171_;
            }
            4 => {
                if v_isShared_5190_ == 0 {
                    v___x_5192_ = v___x_5189_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchKeyRootFor___boxed(
    mut v_e_5195_: *mut leanh::LeanObject,
    mut v_a_5196_: *mut leanh::LeanObject,
    mut v_a_5197_: *mut leanh::LeanObject,
    mut v_a_5198_: *mut leanh::LeanObject,
    mut v_a_5199_: *mut leanh::LeanObject,
    mut v_a_5200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5201_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(
        v_e_5195_, v_a_5196_, v_a_5197_, v_a_5198_, v_a_5199_,
    );
    leanh::lean_dec(v_a_5199_);
    leanh::lean_dec_ref(v_a_5198_);
    leanh::lean_dec(v_a_5197_);
    leanh::lean_dec_ref(v_a_5196_);
    return v_res_5201_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(
    mut v_as_5202_: *mut leanh::LeanObject,
    mut v_sz_5203_: usize,
    mut v_i_5204_: usize,
    mut v_b_5205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5206_: u8 = 0;
    let mut v_a_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: usize = 0;
    let mut v___x_5211_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5206_ = lean_usize_dec_lt(v_i_5204_, v_sz_5203_);
                if v___x_5206_ == 0 {
                    return v_b_5205_;
                } else {
                    v_a_5207_ = lean_array_uget_borrowed(v_as_5202_, v_i_5204_);
                    v_snd_5208_ = leanh::lean_ctor_get(v_a_5207_, 1);
                    v___x_5209_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_snd_5208_, v_b_5205_);
                    v___x_5210_ = 1usize;
                    v___x_5211_ = lean_usize_add(v_i_5204_, v___x_5210_);
                    v_i_5204_ = v___x_5211_;
                    v_b_5205_ = v___x_5209_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(
    mut v_trie_5213_: *mut leanh::LeanObject,
    mut v_result_5214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5218_: usize = 0;
    let mut v___x_5219_: usize = 0;
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_vs_5215_ = leanh::lean_ctor_get(v_trie_5213_, 0);
    v_children_5216_ = leanh::lean_ctor_get(v_trie_5213_, 1);
    v_result_5217_ = l_Array_append___redArg(v_result_5214_, v_vs_5215_);
    v_sz_5218_ = lean_array_size(v_children_5216_);
    v___x_5219_ = 0usize;
    v___x_5220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_children_5216_, v_sz_5218_, v___x_5219_, v_result_5217_);
    return v___x_5220_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg___boxed(
    mut v_trie_5221_: *mut leanh::LeanObject,
    mut v_result_5222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5223_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(
            v_trie_5221_,
            v_result_5222_,
        );
    leanh::lean_dec_ref(v_trie_5221_);
    return v_res_5223_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg___boxed(
    mut v_as_5224_: *mut leanh::LeanObject,
    mut v_sz_5225_: *mut leanh::LeanObject,
    mut v_i_5226_: *mut leanh::LeanObject,
    mut v_b_5227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5228_: usize = 0;
    let mut v_i_boxed_5229_: usize = 0;
    let mut v_res_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5228_ = leanh::lean_unbox_usize(v_sz_5225_);
    leanh::lean_dec(v_sz_5225_);
    v_i_boxed_5229_ = leanh::lean_unbox_usize(v_i_5226_);
    leanh::lean_dec(v_i_5226_);
    v_res_5230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_5224_, v_sz_boxed_5228_, v_i_boxed_5229_, v_b_5227_);
    leanh::lean_dec_ref(v_as_5224_);
    return v_res_5230_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(
    mut v_00_u03b1_5231_: *mut leanh::LeanObject,
    mut v_trie_5232_: *mut leanh::LeanObject,
    mut v_result_5233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5234_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(
            v_trie_5232_,
            v_result_5233_,
        );
    return v___x_5234_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___boxed(
    mut v_00_u03b1_5235_: *mut leanh::LeanObject,
    mut v_trie_5236_: *mut leanh::LeanObject,
    mut v_result_5237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5238_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go(
        v_00_u03b1_5235_,
        v_trie_5236_,
        v_result_5237_,
    );
    leanh::lean_dec_ref(v_trie_5236_);
    return v_res_5238_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(
    mut v_00_u03b1_5239_: *mut leanh::LeanObject,
    mut v_as_5240_: *mut leanh::LeanObject,
    mut v_sz_5241_: usize,
    mut v_i_5242_: usize,
    mut v_b_5243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___redArg(v_as_5240_, v_sz_5241_, v_i_5242_, v_b_5243_);
    return v___x_5244_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0___boxed(
    mut v_00_u03b1_5245_: *mut leanh::LeanObject,
    mut v_as_5246_: *mut leanh::LeanObject,
    mut v_sz_5247_: *mut leanh::LeanObject,
    mut v_i_5248_: *mut leanh::LeanObject,
    mut v_b_5249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5250_: usize = 0;
    let mut v_i_boxed_5251_: usize = 0;
    let mut v_res_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5250_ = leanh::lean_unbox_usize(v_sz_5247_);
    leanh::lean_dec(v_sz_5247_);
    v_i_boxed_5251_ = leanh::lean_unbox_usize(v_i_5248_);
    leanh::lean_dec(v_i_5248_);
    v_res_5252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go_spec__0(v_00_u03b1_5245_, v_as_5246_, v_sz_boxed_5250_, v_i_boxed_5251_, v_b_5249_);
    leanh::lean_dec_ref(v_as_5246_);
    return v_res_5252_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(
    mut v_d_5253_: *mut leanh::LeanObject,
    mut v_k_5254_: *mut leanh::LeanObject,
    mut v_result_5255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5256_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_5253_, v_k_5254_);
    if leanh::lean_obj_tag(v___x_5256_) == 0 {
        return v_result_5255_;
    } else {
        let mut v_val_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_5257_ = leanh::lean_ctor_get(v___x_5256_, 0);
        leanh::lean_inc(v_val_5257_);
        leanh::lean_dec_ref_known(v___x_5256_, 1);
        v___x_5258_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey_go___redArg(v_val_5257_, v_result_5255_);
        leanh::lean_dec(v_val_5257_);
        return v___x_5258_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg___boxed(
    mut v_d_5259_: *mut leanh::LeanObject,
    mut v_k_5260_: *mut leanh::LeanObject,
    mut v_result_5261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5262_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(
            v_d_5259_,
            v_k_5260_,
            v_result_5261_,
        );
    leanh::lean_dec(v_k_5260_);
    leanh::lean_dec_ref(v_d_5259_);
    return v_res_5262_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(
    mut v_00_u03b1_5263_: *mut leanh::LeanObject,
    mut v_d_5264_: *mut leanh::LeanObject,
    mut v_k_5265_: *mut leanh::LeanObject,
    mut v_result_5266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5267_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(
            v_d_5264_,
            v_k_5265_,
            v_result_5266_,
        );
    return v___x_5267_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___boxed(
    mut v_00_u03b1_5268_: *mut leanh::LeanObject,
    mut v_d_5269_: *mut leanh::LeanObject,
    mut v_k_5270_: *mut leanh::LeanObject,
    mut v_result_5271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5272_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey(
        v_00_u03b1_5268_,
        v_d_5269_,
        v_k_5270_,
        v_result_5271_,
    );
    leanh::lean_dec(v_k_5270_);
    leanh::lean_dec_ref(v_d_5269_);
    return v_res_5272_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(
    mut v_d_5273_: *mut leanh::LeanObject,
    mut v_e_5274_: *mut leanh::LeanObject,
    mut v_a_5275_: *mut leanh::LeanObject,
    mut v_a_5276_: *mut leanh::LeanObject,
    mut v_a_5277_: *mut leanh::LeanObject,
    mut v_a_5278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5281_: u8 = 0;
    let mut v_ctxApprox_5282_: u8 = 0;
    let mut v_quasiPatternApprox_5283_: u8 = 0;
    let mut v_constApprox_5284_: u8 = 0;
    let mut v_isDefEqStuckEx_5285_: u8 = 0;
    let mut v_unificationHints_5286_: u8 = 0;
    let mut v_proofIrrelevance_5287_: u8 = 0;
    let mut v_assignSyntheticOpaque_5288_: u8 = 0;
    let mut v_offsetCnstrs_5289_: u8 = 0;
    let mut v_etaStruct_5290_: u8 = 0;
    let mut v_univApprox_5291_: u8 = 0;
    let mut v_iota_5292_: u8 = 0;
    let mut v_beta_5293_: u8 = 0;
    let mut v_proj_5294_: u8 = 0;
    let mut v_zeta_5295_: u8 = 0;
    let mut v_zetaDelta_5296_: u8 = 0;
    let mut v_zetaUnused_5297_: u8 = 0;
    let mut v_zetaHave_5298_: u8 = 0;
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v_trackZetaDelta_5302_: u8 = 0;
    let mut v_zetaDeltaSet_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5309_: u8 = 0;
    let mut v_inTypeClassResolution_5310_: u8 = 0;
    let mut v_cacheInferType_5311_: u8 = 0;
    let mut v___x_5312_: u8 = 0;
    let mut v_config_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: u64 = 0;
    let mut v___x_5316_: u64 = 0;
    let mut v___x_5317_: u64 = 0;
    let mut v___x_5318_: u64 = 0;
    let mut v___x_5319_: u64 = 0;
    let mut v_key_5320_: u64 = 0;
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5327_: u8 = 0;
    let mut v_fst_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v_result_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5341_: u8 = 0;
    let mut v_isSharedCheck_5342_: u8 = 0;
    let mut v_a_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut v_reuseFailAlloc_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5280_ = l_Lean_Meta_Context_config(v_a_5275_);
                v_foApprox_5281_ = leanh::lean_ctor_get_uint8(v___x_5280_, 0 as u32);
                v_ctxApprox_5282_ = leanh::lean_ctor_get_uint8(v___x_5280_, 1 as u32);
                v_quasiPatternApprox_5283_ =
                    leanh::lean_ctor_get_uint8(v___x_5280_, 2 as u32);
                v_constApprox_5284_ = leanh::lean_ctor_get_uint8(v___x_5280_, 3 as u32);
                v_isDefEqStuckEx_5285_ = leanh::lean_ctor_get_uint8(v___x_5280_, 4 as u32);
                v_unificationHints_5286_ = leanh::lean_ctor_get_uint8(v___x_5280_, 5 as u32);
                v_proofIrrelevance_5287_ = leanh::lean_ctor_get_uint8(v___x_5280_, 6 as u32);
                v_assignSyntheticOpaque_5288_ =
                    leanh::lean_ctor_get_uint8(v___x_5280_, 7 as u32);
                v_offsetCnstrs_5289_ = leanh::lean_ctor_get_uint8(v___x_5280_, 8 as u32);
                v_etaStruct_5290_ = leanh::lean_ctor_get_uint8(v___x_5280_, 10 as u32);
                v_univApprox_5291_ = leanh::lean_ctor_get_uint8(v___x_5280_, 11 as u32);
                v_iota_5292_ = leanh::lean_ctor_get_uint8(v___x_5280_, 12 as u32);
                v_beta_5293_ = leanh::lean_ctor_get_uint8(v___x_5280_, 13 as u32);
                v_proj_5294_ = leanh::lean_ctor_get_uint8(v___x_5280_, 14 as u32);
                v_zeta_5295_ = leanh::lean_ctor_get_uint8(v___x_5280_, 15 as u32);
                v_zetaDelta_5296_ = leanh::lean_ctor_get_uint8(v___x_5280_, 16 as u32);
                v_zetaUnused_5297_ = leanh::lean_ctor_get_uint8(v___x_5280_, 17 as u32);
                v_zetaHave_5298_ = leanh::lean_ctor_get_uint8(v___x_5280_, 18 as u32);
                v_isSharedCheck_5352_ = (!leanh::lean_is_exclusive(v___x_5280_)) as u8;
                if v_isSharedCheck_5352_ == 0 {
                    v___x_5300_ = v___x_5280_;
                    v_isShared_5301_ = v_isSharedCheck_5352_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5280_);
                    v___x_5300_ = leanh::lean_box(0);
                    v_isShared_5301_ = v_isSharedCheck_5352_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_5302_ = leanh::lean_ctor_get_uint8(
                    v_a_5275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5303_ = leanh::lean_ctor_get(v_a_5275_, 1);
                v_lctx_5304_ = leanh::lean_ctor_get(v_a_5275_, 2);
                v_localInstances_5305_ = leanh::lean_ctor_get(v_a_5275_, 3);
                v_defEqCtx_x3f_5306_ = leanh::lean_ctor_get(v_a_5275_, 4);
                v_synthPendingDepth_5307_ = leanh::lean_ctor_get(v_a_5275_, 5);
                v_canUnfold_x3f_5308_ = leanh::lean_ctor_get(v_a_5275_, 6);
                v_univApprox_5309_ = leanh::lean_ctor_get_uint8(
                    v_a_5275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5310_ = leanh::lean_ctor_get_uint8(
                    v_a_5275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5311_ = leanh::lean_ctor_get_uint8(
                    v_a_5275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5312_ = 2;
                if v_isShared_5301_ == 0 {
                    v_config_5314_ = v___x_5300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5351_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        0 as u32,
                        v_foApprox_5281_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        1 as u32,
                        v_ctxApprox_5282_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        2 as u32,
                        v_quasiPatternApprox_5283_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        3 as u32,
                        v_constApprox_5284_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        4 as u32,
                        v_isDefEqStuckEx_5285_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        5 as u32,
                        v_unificationHints_5286_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        6 as u32,
                        v_proofIrrelevance_5287_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        7 as u32,
                        v_assignSyntheticOpaque_5288_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        8 as u32,
                        v_offsetCnstrs_5289_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        10 as u32,
                        v_etaStruct_5290_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        11 as u32,
                        v_univApprox_5291_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        12 as u32,
                        v_iota_5292_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        13 as u32,
                        v_beta_5293_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        14 as u32,
                        v_proj_5294_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        15 as u32,
                        v_zeta_5295_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        16 as u32,
                        v_zetaDelta_5296_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        17 as u32,
                        v_zetaUnused_5297_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5351_,
                        18 as u32,
                        v_zetaHave_5298_,
                    );
                    v_config_5314_ = v_reuseFailAlloc_5351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_5314_, 9 as u32, v___x_5312_);
                v___x_5315_ = l_Lean_Meta_Context_configKey(v_a_5275_);
                v___x_5316_ = 3u64;
                v___x_5317_ = lean_uint64_shift_right(v___x_5315_, v___x_5316_);
                v___x_5318_ = lean_uint64_shift_left(v___x_5317_, v___x_5316_);
                v___x_5319_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0_once),
                    _init_l_Lean_Meta_DiscrTree_mkPath___closed__0,
                );
                v_key_5320_ = lean_uint64_lor(v___x_5318_, v___x_5319_);
                v___x_5321_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_5321_, 0, v_config_5314_);
                leanh::lean_ctor_set_uint64(
                    v___x_5321_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_5320_,
                );
                leanh::lean_inc(v_canUnfold_x3f_5308_);
                leanh::lean_inc(v_synthPendingDepth_5307_);
                leanh::lean_inc(v_defEqCtx_x3f_5306_);
                leanh::lean_inc_ref(v_localInstances_5305_);
                leanh::lean_inc_ref(v_lctx_5304_);
                leanh::lean_inc(v_zetaDeltaSet_5303_);
                v___x_5322_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_5322_, 0, v___x_5321_);
                leanh::lean_ctor_set(v___x_5322_, 1, v_zetaDeltaSet_5303_);
                leanh::lean_ctor_set(v___x_5322_, 2, v_lctx_5304_);
                leanh::lean_ctor_set(v___x_5322_, 3, v_localInstances_5305_);
                leanh::lean_ctor_set(v___x_5322_, 4, v_defEqCtx_x3f_5306_);
                leanh::lean_ctor_set(v___x_5322_, 5, v_synthPendingDepth_5307_);
                leanh::lean_ctor_set(v___x_5322_, 6, v_canUnfold_x3f_5308_);
                leanh::lean_ctor_set_uint8(
                    v___x_5322_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5302_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5322_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5309_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5322_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5310_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5322_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5311_,
                );
                v___x_5323_ = l_Lean_Meta_DiscrTree_getMatchKeyRootFor(
                    v_e_5274_,
                    v___x_5322_,
                    v_a_5276_,
                    v_a_5277_,
                    v_a_5278_,
                );
                leanh::lean_dec_ref_known(v___x_5322_, 7);
                if leanh::lean_obj_tag(v___x_5323_) == 0 {
                    v_a_5324_ = leanh::lean_ctor_get(v___x_5323_, 0);
                    v_isSharedCheck_5342_ = (!leanh::lean_is_exclusive(v___x_5323_)) as u8;
                    if v_isSharedCheck_5342_ == 0 {
                        v___x_5326_ = v___x_5323_;
                        v_isShared_5327_ = v_isSharedCheck_5342_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5324_);
                        leanh::lean_dec(v___x_5323_);
                        v___x_5326_ = leanh::lean_box(0);
                        v_isShared_5327_ = v_isSharedCheck_5342_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5343_ = leanh::lean_ctor_get(v___x_5323_, 0);
                    v_isSharedCheck_5350_ = (!leanh::lean_is_exclusive(v___x_5323_)) as u8;
                    if v_isSharedCheck_5350_ == 0 {
                        v___x_5345_ = v___x_5323_;
                        v_isShared_5346_ = v_isSharedCheck_5350_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5343_);
                        leanh::lean_dec(v___x_5323_);
                        v___x_5345_ = leanh::lean_box(0);
                        v_isShared_5346_ = v_isSharedCheck_5350_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_5328_ = leanh::lean_ctor_get(v_a_5324_, 0);
                v_snd_5329_ = leanh::lean_ctor_get(v_a_5324_, 1);
                v_isSharedCheck_5341_ = (!leanh::lean_is_exclusive(v_a_5324_)) as u8;
                if v_isSharedCheck_5341_ == 0 {
                    v___x_5331_ = v_a_5324_;
                    v_isShared_5332_ = v_isSharedCheck_5341_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5329_);
                    leanh::lean_inc(v_fst_5328_);
                    leanh::lean_dec(v_a_5324_);
                    v___x_5331_ = leanh::lean_box(0);
                    v_isShared_5332_ = v_isSharedCheck_5341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_result_5333_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_5273_);
                v___x_5334_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getAllValuesForKey___redArg(v_d_5273_, v_fst_5328_, v_result_5333_);
                leanh::lean_dec(v_fst_5328_);
                if v_isShared_5332_ == 0 {
                    leanh::lean_ctor_set(v___x_5331_, 0, v___x_5334_);
                    v___x_5336_ = v___x_5331_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5340_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5340_, 0, v___x_5334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5340_, 1, v_snd_5329_);
                    v___x_5336_ = v_reuseFailAlloc_5340_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5327_ == 0 {
                    leanh::lean_ctor_set(v___x_5326_, 0, v___x_5336_);
                    v___x_5338_ = v___x_5326_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5339_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5339_, 0, v___x_5336_);
                    v___x_5338_ = v_reuseFailAlloc_5339_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5338_;
            }
            7 => {
                if v_isShared_5346_ == 0 {
                    v___x_5348_ = v___x_5345_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
                    v___x_5348_ = v_reuseFailAlloc_5349_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchLiberal___redArg___boxed(
    mut v_d_5353_: *mut leanh::LeanObject,
    mut v_e_5354_: *mut leanh::LeanObject,
    mut v_a_5355_: *mut leanh::LeanObject,
    mut v_a_5356_: *mut leanh::LeanObject,
    mut v_a_5357_: *mut leanh::LeanObject,
    mut v_a_5358_: *mut leanh::LeanObject,
    mut v_a_5359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5360_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(
        v_d_5353_, v_e_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_,
    );
    leanh::lean_dec(v_a_5358_);
    leanh::lean_dec_ref(v_a_5357_);
    leanh::lean_dec(v_a_5356_);
    leanh::lean_dec_ref(v_a_5355_);
    leanh::lean_dec_ref(v_d_5353_);
    return v_res_5360_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchLiberal(
    mut v_00_u03b1_5361_: *mut leanh::LeanObject,
    mut v_d_5362_: *mut leanh::LeanObject,
    mut v_e_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
    mut v_a_5365_: *mut leanh::LeanObject,
    mut v_a_5366_: *mut leanh::LeanObject,
    mut v_a_5367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5369_ = l_Lean_Meta_DiscrTree_getMatchLiberal___redArg(
        v_d_5362_, v_e_5363_, v_a_5364_, v_a_5365_, v_a_5366_, v_a_5367_,
    );
    return v___x_5369_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getMatchLiberal___boxed(
    mut v_00_u03b1_5370_: *mut leanh::LeanObject,
    mut v_d_5371_: *mut leanh::LeanObject,
    mut v_e_5372_: *mut leanh::LeanObject,
    mut v_a_5373_: *mut leanh::LeanObject,
    mut v_a_5374_: *mut leanh::LeanObject,
    mut v_a_5375_: *mut leanh::LeanObject,
    mut v_a_5376_: *mut leanh::LeanObject,
    mut v_a_5377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5378_ = l_Lean_Meta_DiscrTree_getMatchLiberal(
        v_00_u03b1_5370_,
        v_d_5371_,
        v_e_5372_,
        v_a_5373_,
        v_a_5374_,
        v_a_5375_,
        v_a_5376_,
    );
    leanh::lean_dec(v_a_5376_);
    leanh::lean_dec_ref(v_a_5375_);
    leanh::lean_dec(v_a_5374_);
    leanh::lean_dec_ref(v_a_5373_);
    leanh::lean_dec_ref(v_d_5371_);
    return v_res_5378_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(
    mut v_n_5379_: *mut leanh::LeanObject,
    mut v_todo_5380_: *mut leanh::LeanObject,
    mut v_as_5381_: *mut leanh::LeanObject,
    mut v_i_5382_: usize,
    mut v_stop_5383_: usize,
    mut v_b_5384_: *mut leanh::LeanObject,
    mut v___y_5385_: *mut leanh::LeanObject,
    mut v___y_5386_: *mut leanh::LeanObject,
    mut v___y_5387_: *mut leanh::LeanObject,
    mut v___y_5388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5390_: u8 = 0;
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: usize = 0;
    let mut v___x_5399_: usize = 0;
    let mut v___x_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5390_ = lean_usize_dec_eq(v_i_5382_, v_stop_5383_);
                if v___x_5390_ == 0 {
                    v___x_5391_ = lean_array_uget_borrowed(v_as_5381_, v_i_5382_);
                    v_fst_5392_ = leanh::lean_ctor_get(v___x_5391_, 0);
                    v_snd_5393_ = leanh::lean_ctor_get(v___x_5391_, 1);
                    v___x_5394_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_5392_);
                    v___x_5395_ = lean_nat_add(v_n_5379_, v___x_5394_);
                    leanh::lean_dec(v___x_5394_);
                    leanh::lean_inc(v_snd_5393_);
                    leanh::lean_inc_ref(v_todo_5380_);
                    v___x_5396_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_5395_, v_todo_5380_, v_snd_5393_, v_b_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
                    if leanh::lean_obj_tag(v___x_5396_) == 0 {
                        v_a_5397_ = leanh::lean_ctor_get(v___x_5396_, 0);
                        leanh::lean_inc(v_a_5397_);
                        leanh::lean_dec_ref_known(v___x_5396_, 1);
                        v___x_5398_ = 1usize;
                        v___x_5399_ = lean_usize_add(v_i_5382_, v___x_5398_);
                        v_i_5382_ = v___x_5399_;
                        v_b_5384_ = v_a_5397_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_todo_5380_);
                        return v___x_5396_;
                    }
                } else {
                    leanh::lean_dec_ref(v_todo_5380_);
                    v___x_5401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5401_, 0, v_b_5384_);
                    return v___x_5401_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(
    mut v_skip_5402_: *mut leanh::LeanObject,
    mut v_todo_5403_: *mut leanh::LeanObject,
    mut v_c_5404_: *mut leanh::LeanObject,
    mut v_result_5405_: *mut leanh::LeanObject,
    mut v_a_5406_: *mut leanh::LeanObject,
    mut v_a_5407_: *mut leanh::LeanObject,
    mut v_a_5408_: *mut leanh::LeanObject,
    mut v_a_5409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5412_: u8 = 0;
    let mut v_vs_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: u8 = 0;
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: u8 = 0;
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5427_: u8 = 0;
    let mut v_fst_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v_todo_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: u8 = 0;
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: u8 = 0;
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: u8 = 0;
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: u8 = 0;
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: usize = 0;
    let mut v___x_5458_: usize = 0;
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: usize = 0;
    let mut v___x_5461_: usize = 0;
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: u8 = 0;
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5474_: u8 = 0;
    let mut v_isSharedCheck_5475_: u8 = 0;
    let mut v_a_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5479_: u8 = 0;
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5483_: u8 = 0;
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: u8 = 0;
    let mut v___x_5490_: u8 = 0;
    let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: u8 = 0;
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: usize = 0;
    let mut v___x_5497_: usize = 0;
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: usize = 0;
    let mut v___x_5500_: usize = 0;
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5411_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5412_ = lean_nat_dec_eq(v_skip_5402_, v_zero_5411_);
                if v_isZero_5412_ == 1 {
                    leanh::lean_dec(v_skip_5402_);
                    v_vs_5413_ = leanh::lean_ctor_get(v_c_5404_, 0);
                    leanh::lean_inc_ref(v_vs_5413_);
                    v_children_5414_ = leanh::lean_ctor_get(v_c_5404_, 1);
                    leanh::lean_inc_ref(v_children_5414_);
                    leanh::lean_dec_ref(v_c_5404_);
                    v___x_5415_ = lean_array_get_size(v_todo_5403_);
                    v___x_5416_ = lean_nat_dec_eq(v___x_5415_, v_zero_5411_);
                    if v___x_5416_ == 0 {
                        leanh::lean_dec_ref(v_vs_5413_);
                        v___x_5417_ = lean_array_get_size(v_children_5414_);
                        v___x_5418_ = lean_nat_dec_eq(v___x_5417_, v_zero_5411_);
                        if v___x_5418_ == 0 {
                            v___x_5419_ = l_Lean_instInhabitedExpr;
                            v___x_5420_ = leanh::lean_unsigned_to_nat(1);
                            v___x_5421_ = lean_nat_sub(v___x_5415_, v___x_5420_);
                            v_e_5422_ =
                                lean_array_get_borrowed(v___x_5419_, v_todo_5403_, v___x_5421_);
                            leanh::lean_dec(v___x_5421_);
                            leanh::lean_inc(v_e_5422_);
                            v___x_5423_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(v_e_5422_, v___x_5418_, v___x_5418_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
                            if leanh::lean_obj_tag(v___x_5423_) == 0 {
                                v_a_5424_ = leanh::lean_ctor_get(v___x_5423_, 0);
                                v_isSharedCheck_5475_ =
                                    (!leanh::lean_is_exclusive(v___x_5423_)) as u8;
                                if v_isSharedCheck_5475_ == 0 {
                                    v___x_5426_ = v___x_5423_;
                                    v_isShared_5427_ = v_isSharedCheck_5475_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5424_);
                                    leanh::lean_dec(v___x_5423_);
                                    v___x_5426_ = leanh::lean_box(0);
                                    v_isShared_5427_ = v_isSharedCheck_5475_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_children_5414_);
                                leanh::lean_dec_ref(v_result_5405_);
                                leanh::lean_dec_ref(v_todo_5403_);
                                v_a_5476_ = leanh::lean_ctor_get(v___x_5423_, 0);
                                v_isSharedCheck_5483_ =
                                    (!leanh::lean_is_exclusive(v___x_5423_)) as u8;
                                if v_isSharedCheck_5483_ == 0 {
                                    v___x_5478_ = v___x_5423_;
                                    v_isShared_5479_ = v_isSharedCheck_5483_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5476_);
                                    leanh::lean_dec(v___x_5423_);
                                    v___x_5478_ = leanh::lean_box(0);
                                    v_isShared_5479_ = v_isSharedCheck_5483_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_children_5414_);
                            leanh::lean_dec_ref(v_todo_5403_);
                            v___x_5484_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5484_, 0, v_result_5405_);
                            return v___x_5484_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_children_5414_);
                        leanh::lean_dec_ref(v_todo_5403_);
                        v___x_5485_ = l_Array_append___redArg(v_result_5405_, v_vs_5413_);
                        leanh::lean_dec_ref(v_vs_5413_);
                        v___x_5486_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5486_, 0, v___x_5485_);
                        return v___x_5486_;
                    }
                } else {
                    v_children_5487_ = leanh::lean_ctor_get(v_c_5404_, 1);
                    leanh::lean_inc_ref(v_children_5487_);
                    leanh::lean_dec_ref(v_c_5404_);
                    v___x_5488_ = lean_array_get_size(v_children_5487_);
                    v___x_5489_ = lean_nat_dec_eq(v___x_5488_, v_zero_5411_);
                    if v___x_5489_ == 0 {
                        v___x_5490_ = lean_nat_dec_lt(v_zero_5411_, v___x_5488_);
                        if v___x_5490_ == 0 {
                            leanh::lean_dec_ref(v_children_5487_);
                            leanh::lean_dec_ref(v_todo_5403_);
                            leanh::lean_dec(v_skip_5402_);
                            v___x_5491_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5491_, 0, v_result_5405_);
                            return v___x_5491_;
                        } else {
                            v_one_5492_ = leanh::lean_unsigned_to_nat(1);
                            v_n_5493_ = lean_nat_sub(v_skip_5402_, v_one_5492_);
                            leanh::lean_dec(v_skip_5402_);
                            v___x_5494_ = lean_nat_dec_le(v___x_5488_, v___x_5488_);
                            if v___x_5494_ == 0 {
                                if v___x_5490_ == 0 {
                                    leanh::lean_dec(v_n_5493_);
                                    leanh::lean_dec_ref(v_children_5487_);
                                    leanh::lean_dec_ref(v_todo_5403_);
                                    v___x_5495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_5495_, 0, v_result_5405_);
                                    return v___x_5495_;
                                } else {
                                    v___x_5496_ = 0usize;
                                    v___x_5497_ = lean_usize_of_nat(v___x_5488_);
                                    v___x_5498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_5493_, v_todo_5403_, v_children_5487_, v___x_5496_, v___x_5497_, v_result_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
                                    leanh::lean_dec_ref(v_children_5487_);
                                    leanh::lean_dec(v_n_5493_);
                                    return v___x_5498_;
                                }
                            } else {
                                v___x_5499_ = 0usize;
                                v___x_5500_ = lean_usize_of_nat(v___x_5488_);
                                v___x_5501_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_5493_, v_todo_5403_, v_children_5487_, v___x_5499_, v___x_5500_, v_result_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
                                leanh::lean_dec_ref(v_children_5487_);
                                leanh::lean_dec(v_n_5493_);
                                return v___x_5501_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_children_5487_);
                        leanh::lean_dec_ref(v_todo_5403_);
                        leanh::lean_dec(v_skip_5402_);
                        v___x_5502_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5502_, 0, v_result_5405_);
                        return v___x_5502_;
                    }
                }
            }
            1 => {
                v_fst_5428_ = leanh::lean_ctor_get(v_a_5424_, 0);
                v_snd_5429_ = leanh::lean_ctor_get(v_a_5424_, 1);
                v_isSharedCheck_5474_ = (!leanh::lean_is_exclusive(v_a_5424_)) as u8;
                if v_isSharedCheck_5474_ == 0 {
                    v___x_5431_ = v_a_5424_;
                    v_isShared_5432_ = v_isSharedCheck_5474_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5429_);
                    leanh::lean_inc(v_fst_5428_);
                    leanh::lean_dec(v_a_5424_);
                    v___x_5431_ = leanh::lean_box(0);
                    v_isShared_5432_ = v_isSharedCheck_5474_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_todo_5433_ = lean_array_pop(v_todo_5403_);
                if leanh::lean_obj_tag(v_fst_5428_) == 0 {
                    leanh::lean_del_object(v___x_5431_);
                    leanh::lean_dec(v_snd_5429_);
                    v___x_5449_ = lean_nat_dec_lt(v_zero_5411_, v___x_5417_);
                    if v___x_5449_ == 0 {
                        leanh::lean_dec_ref(v_todo_5433_);
                        leanh::lean_dec_ref(v_children_5414_);
                        if v_isShared_5427_ == 0 {
                            leanh::lean_ctor_set(v___x_5426_, 0, v_result_5405_);
                            v___x_5451_ = v___x_5426_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_5452_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_result_5405_);
                            v___x_5451_ = v_reuseFailAlloc_5452_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_5453_ = lean_nat_dec_le(v___x_5417_, v___x_5417_);
                        if v___x_5453_ == 0 {
                            if v___x_5449_ == 0 {
                                leanh::lean_dec_ref(v_todo_5433_);
                                leanh::lean_dec_ref(v_children_5414_);
                                if v_isShared_5427_ == 0 {
                                    leanh::lean_ctor_set(v___x_5426_, 0, v_result_5405_);
                                    v___x_5455_ = v___x_5426_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5456_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5456_,
                                        0,
                                        v_result_5405_,
                                    );
                                    v___x_5455_ = v_reuseFailAlloc_5456_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_5426_);
                                v___x_5457_ = 0usize;
                                v___x_5458_ = lean_usize_of_nat(v___x_5417_);
                                v___x_5459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_5433_, v_children_5414_, v___x_5457_, v___x_5458_, v_result_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
                                leanh::lean_dec_ref(v_children_5414_);
                                return v___x_5459_;
                            }
                        } else {
                            leanh::lean_del_object(v___x_5426_);
                            v___x_5460_ = 0usize;
                            v___x_5461_ = lean_usize_of_nat(v___x_5417_);
                            v___x_5462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_5433_, v_children_5414_, v___x_5460_, v___x_5461_, v_result_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
                            leanh::lean_dec_ref(v_children_5414_);
                            return v___x_5462_;
                        }
                    }
                } else {
                    v___x_5463_ = leanh::lean_box(0);
                    v___x_5464_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1_once), _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop___redArg___closed__1);
                    v___x_5465_ =
                        lean_array_get_borrowed(v___x_5464_, v_children_5414_, v_zero_5411_);
                    v_fst_5466_ = leanh::lean_ctor_get(v___x_5465_, 0);
                    v_snd_5467_ = leanh::lean_ctor_get(v___x_5465_, 1);
                    v___x_5468_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_fst_5466_, v___x_5463_);
                    if v___x_5468_ == 0 {
                        leanh::lean_inc_ref(v_result_5405_);
                        if v_isShared_5427_ == 0 {
                            leanh::lean_ctor_set(v___x_5426_, 0, v_result_5405_);
                            v___x_5470_ = v___x_5426_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_5471_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_result_5405_);
                            v___x_5470_ = v_reuseFailAlloc_5471_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5426_);
                        leanh::lean_inc(v_snd_5467_);
                        leanh::lean_inc_ref(v_todo_5433_);
                        v___x_5472_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v_zero_5411_, v_todo_5433_, v_snd_5467_, v_result_5405_, v_a_5406_, v_a_5407_, v_a_5408_, v_a_5409_);
                        if leanh::lean_obj_tag(v___x_5472_) == 0 {
                            v_a_5473_ = leanh::lean_ctor_get(v___x_5472_, 0);
                            leanh::lean_inc(v_a_5473_);
                            v___y_5435_ = v___x_5472_;
                            v_a_5436_ = v_a_5473_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_todo_5433_);
                            leanh::lean_del_object(v___x_5431_);
                            leanh::lean_dec(v_snd_5429_);
                            leanh::lean_dec(v_fst_5428_);
                            leanh::lean_dec_ref(v_children_5414_);
                            return v___x_5472_;
                        }
                    }
                }
            }
            3 => {
                v___x_5437_ = lean_nat_dec_lt(v_zero_5411_, v___x_5417_);
                if v___x_5437_ == 0 {
                    leanh::lean_dec_ref(v_a_5436_);
                    leanh::lean_dec_ref(v_todo_5433_);
                    leanh::lean_del_object(v___x_5431_);
                    leanh::lean_dec(v_snd_5429_);
                    leanh::lean_dec(v_fst_5428_);
                    leanh::lean_dec_ref(v_children_5414_);
                    return v___y_5435_;
                } else {
                    v___x_5438_ = lean_nat_sub(v___x_5417_, v___x_5420_);
                    v___x_5439_ = lean_nat_dec_le(v_zero_5411_, v___x_5438_);
                    if v___x_5439_ == 0 {
                        leanh::lean_dec(v___x_5438_);
                        leanh::lean_dec_ref(v_a_5436_);
                        leanh::lean_dec_ref(v_todo_5433_);
                        leanh::lean_del_object(v___x_5431_);
                        leanh::lean_dec(v_snd_5429_);
                        leanh::lean_dec(v_fst_5428_);
                        leanh::lean_dec_ref(v_children_5414_);
                        return v___y_5435_;
                    } else {
                        v___x_5440_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__2;
                        if v_isShared_5432_ == 0 {
                            leanh::lean_ctor_set(v___x_5431_, 1, v___x_5440_);
                            v___x_5442_ = v___x_5431_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5448_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_fst_5428_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5448_, 1, v___x_5440_);
                            v___x_5442_ = v_reuseFailAlloc_5448_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_5443_ = l_Array_binSearchAux___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getMatchLoop_spec__0___redArg(v_children_5414_, v___x_5442_, v_zero_5411_, v___x_5438_);
                leanh::lean_dec_ref(v___x_5442_);
                leanh::lean_dec_ref(v_children_5414_);
                if leanh::lean_obj_tag(v___x_5443_) == 0 {
                    leanh::lean_dec_ref(v_a_5436_);
                    leanh::lean_dec_ref(v_todo_5433_);
                    leanh::lean_dec(v_snd_5429_);
                    return v___y_5435_;
                } else {
                    leanh::lean_dec_ref(v___y_5435_);
                    v_val_5444_ = leanh::lean_ctor_get(v___x_5443_, 0);
                    leanh::lean_inc(v_val_5444_);
                    leanh::lean_dec_ref_known(v___x_5443_, 1);
                    v_snd_5445_ = leanh::lean_ctor_get(v_val_5444_, 1);
                    leanh::lean_inc(v_snd_5445_);
                    leanh::lean_dec(v_val_5444_);
                    v___x_5446_ = l_Array_append___redArg(v_todo_5433_, v_snd_5429_);
                    leanh::lean_dec(v_snd_5429_);
                    v_skip_5402_ = v_zero_5411_;
                    v_todo_5403_ = v___x_5446_;
                    v_c_5404_ = v_snd_5445_;
                    v_result_5405_ = v_a_5436_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                return v___x_5451_;
            }
            6 => {
                return v___x_5455_;
            }
            7 => {
                v___y_5435_ = v___x_5470_;
                v_a_5436_ = v_result_5405_;
                state = 3;
                continue;
            }
            8 => {
                if v_isShared_5479_ == 0 {
                    v___x_5481_ = v___x_5478_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5482_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
                    v___x_5481_ = v_reuseFailAlloc_5482_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(
    mut v_todo_5503_: *mut leanh::LeanObject,
    mut v_as_5504_: *mut leanh::LeanObject,
    mut v_i_5505_: usize,
    mut v_stop_5506_: usize,
    mut v_b_5507_: *mut leanh::LeanObject,
    mut v___y_5508_: *mut leanh::LeanObject,
    mut v___y_5509_: *mut leanh::LeanObject,
    mut v___y_5510_: *mut leanh::LeanObject,
    mut v___y_5511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5513_: u8 = 0;
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: usize = 0;
    let mut v___x_5521_: usize = 0;
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5513_ = lean_usize_dec_eq(v_i_5505_, v_stop_5506_);
                if v___x_5513_ == 0 {
                    v___x_5514_ = lean_array_uget_borrowed(v_as_5504_, v_i_5505_);
                    v_fst_5515_ = leanh::lean_ctor_get(v___x_5514_, 0);
                    v_snd_5516_ = leanh::lean_ctor_get(v___x_5514_, 1);
                    v___x_5517_ = l_Lean_Meta_DiscrTree_Key_arity(v_fst_5515_);
                    leanh::lean_inc(v_snd_5516_);
                    leanh::lean_inc_ref(v_todo_5503_);
                    v___x_5518_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_5517_, v_todo_5503_, v_snd_5516_, v_b_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_);
                    if leanh::lean_obj_tag(v___x_5518_) == 0 {
                        v_a_5519_ = leanh::lean_ctor_get(v___x_5518_, 0);
                        leanh::lean_inc(v_a_5519_);
                        leanh::lean_dec_ref_known(v___x_5518_, 1);
                        v___x_5520_ = 1usize;
                        v___x_5521_ = lean_usize_add(v_i_5505_, v___x_5520_);
                        v_i_5505_ = v___x_5521_;
                        v_b_5507_ = v_a_5519_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_todo_5503_);
                        return v___x_5518_;
                    }
                } else {
                    leanh::lean_dec_ref(v_todo_5503_);
                    v___x_5523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5523_, 0, v_b_5507_);
                    return v___x_5523_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg___boxed(
    mut v_todo_5524_: *mut leanh::LeanObject,
    mut v_as_5525_: *mut leanh::LeanObject,
    mut v_i_5526_: *mut leanh::LeanObject,
    mut v_stop_5527_: *mut leanh::LeanObject,
    mut v_b_5528_: *mut leanh::LeanObject,
    mut v___y_5529_: *mut leanh::LeanObject,
    mut v___y_5530_: *mut leanh::LeanObject,
    mut v___y_5531_: *mut leanh::LeanObject,
    mut v___y_5532_: *mut leanh::LeanObject,
    mut v___y_5533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5534_: usize = 0;
    let mut v_stop_boxed_5535_: usize = 0;
    let mut v_res_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5534_ = leanh::lean_unbox_usize(v_i_5526_);
    leanh::lean_dec(v_i_5526_);
    v_stop_boxed_5535_ = leanh::lean_unbox_usize(v_stop_5527_);
    leanh::lean_dec(v_stop_5527_);
    v_res_5536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_5524_, v_as_5525_, v_i_boxed_5534_, v_stop_boxed_5535_, v_b_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
    leanh::lean_dec(v___y_5532_);
    leanh::lean_dec_ref(v___y_5531_);
    leanh::lean_dec(v___y_5530_);
    leanh::lean_dec_ref(v___y_5529_);
    leanh::lean_dec_ref(v_as_5525_);
    return v_res_5536_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg___boxed(
    mut v_n_5537_: *mut leanh::LeanObject,
    mut v_todo_5538_: *mut leanh::LeanObject,
    mut v_as_5539_: *mut leanh::LeanObject,
    mut v_i_5540_: *mut leanh::LeanObject,
    mut v_stop_5541_: *mut leanh::LeanObject,
    mut v_b_5542_: *mut leanh::LeanObject,
    mut v___y_5543_: *mut leanh::LeanObject,
    mut v___y_5544_: *mut leanh::LeanObject,
    mut v___y_5545_: *mut leanh::LeanObject,
    mut v___y_5546_: *mut leanh::LeanObject,
    mut v___y_5547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5548_: usize = 0;
    let mut v_stop_boxed_5549_: usize = 0;
    let mut v_res_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5548_ = leanh::lean_unbox_usize(v_i_5540_);
    leanh::lean_dec(v_i_5540_);
    v_stop_boxed_5549_ = leanh::lean_unbox_usize(v_stop_5541_);
    leanh::lean_dec(v_stop_5541_);
    v_res_5550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_5537_, v_todo_5538_, v_as_5539_, v_i_boxed_5548_, v_stop_boxed_5549_, v_b_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
    leanh::lean_dec(v___y_5546_);
    leanh::lean_dec_ref(v___y_5545_);
    leanh::lean_dec(v___y_5544_);
    leanh::lean_dec_ref(v___y_5543_);
    leanh::lean_dec_ref(v_as_5539_);
    leanh::lean_dec(v_n_5537_);
    return v_res_5550_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg___boxed(
    mut v_skip_5551_: *mut leanh::LeanObject,
    mut v_todo_5552_: *mut leanh::LeanObject,
    mut v_c_5553_: *mut leanh::LeanObject,
    mut v_result_5554_: *mut leanh::LeanObject,
    mut v_a_5555_: *mut leanh::LeanObject,
    mut v_a_5556_: *mut leanh::LeanObject,
    mut v_a_5557_: *mut leanh::LeanObject,
    mut v_a_5558_: *mut leanh::LeanObject,
    mut v_a_5559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5560_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(
            v_skip_5551_,
            v_todo_5552_,
            v_c_5553_,
            v_result_5554_,
            v_a_5555_,
            v_a_5556_,
            v_a_5557_,
            v_a_5558_,
        );
    leanh::lean_dec(v_a_5558_);
    leanh::lean_dec_ref(v_a_5557_);
    leanh::lean_dec(v_a_5556_);
    leanh::lean_dec_ref(v_a_5555_);
    return v_res_5560_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(
    mut v_00_u03b1_5561_: *mut leanh::LeanObject,
    mut v_skip_5562_: *mut leanh::LeanObject,
    mut v_todo_5563_: *mut leanh::LeanObject,
    mut v_c_5564_: *mut leanh::LeanObject,
    mut v_result_5565_: *mut leanh::LeanObject,
    mut v_a_5566_: *mut leanh::LeanObject,
    mut v_a_5567_: *mut leanh::LeanObject,
    mut v_a_5568_: *mut leanh::LeanObject,
    mut v_a_5569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5571_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(
            v_skip_5562_,
            v_todo_5563_,
            v_c_5564_,
            v_result_5565_,
            v_a_5566_,
            v_a_5567_,
            v_a_5568_,
            v_a_5569_,
        );
    return v___x_5571_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___boxed(
    mut v_00_u03b1_5572_: *mut leanh::LeanObject,
    mut v_skip_5573_: *mut leanh::LeanObject,
    mut v_todo_5574_: *mut leanh::LeanObject,
    mut v_c_5575_: *mut leanh::LeanObject,
    mut v_result_5576_: *mut leanh::LeanObject,
    mut v_a_5577_: *mut leanh::LeanObject,
    mut v_a_5578_: *mut leanh::LeanObject,
    mut v_a_5579_: *mut leanh::LeanObject,
    mut v_a_5580_: *mut leanh::LeanObject,
    mut v_a_5581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5582_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process(
        v_00_u03b1_5572_,
        v_skip_5573_,
        v_todo_5574_,
        v_c_5575_,
        v_result_5576_,
        v_a_5577_,
        v_a_5578_,
        v_a_5579_,
        v_a_5580_,
    );
    leanh::lean_dec(v_a_5580_);
    leanh::lean_dec_ref(v_a_5579_);
    leanh::lean_dec(v_a_5578_);
    leanh::lean_dec_ref(v_a_5577_);
    return v_res_5582_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(
    mut v_00_u03b1_5583_: *mut leanh::LeanObject,
    mut v_todo_5584_: *mut leanh::LeanObject,
    mut v_as_5585_: *mut leanh::LeanObject,
    mut v_i_5586_: usize,
    mut v_stop_5587_: usize,
    mut v_b_5588_: *mut leanh::LeanObject,
    mut v___y_5589_: *mut leanh::LeanObject,
    mut v___y_5590_: *mut leanh::LeanObject,
    mut v___y_5591_: *mut leanh::LeanObject,
    mut v___y_5592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___redArg(v_todo_5584_, v_as_5585_, v_i_5586_, v_stop_5587_, v_b_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_);
    return v___x_5594_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0___boxed(
    mut v_00_u03b1_5595_: *mut leanh::LeanObject,
    mut v_todo_5596_: *mut leanh::LeanObject,
    mut v_as_5597_: *mut leanh::LeanObject,
    mut v_i_5598_: *mut leanh::LeanObject,
    mut v_stop_5599_: *mut leanh::LeanObject,
    mut v_b_5600_: *mut leanh::LeanObject,
    mut v___y_5601_: *mut leanh::LeanObject,
    mut v___y_5602_: *mut leanh::LeanObject,
    mut v___y_5603_: *mut leanh::LeanObject,
    mut v___y_5604_: *mut leanh::LeanObject,
    mut v___y_5605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5606_: usize = 0;
    let mut v_stop_boxed_5607_: usize = 0;
    let mut v_res_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5606_ = leanh::lean_unbox_usize(v_i_5598_);
    leanh::lean_dec(v_i_5598_);
    v_stop_boxed_5607_ = leanh::lean_unbox_usize(v_stop_5599_);
    leanh::lean_dec(v_stop_5599_);
    v_res_5608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__0(v_00_u03b1_5595_, v_todo_5596_, v_as_5597_, v_i_boxed_5606_, v_stop_boxed_5607_, v_b_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
    leanh::lean_dec(v___y_5604_);
    leanh::lean_dec_ref(v___y_5603_);
    leanh::lean_dec(v___y_5602_);
    leanh::lean_dec_ref(v___y_5601_);
    leanh::lean_dec_ref(v_as_5597_);
    return v_res_5608_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(
    mut v_00_u03b1_5609_: *mut leanh::LeanObject,
    mut v_n_5610_: *mut leanh::LeanObject,
    mut v_todo_5611_: *mut leanh::LeanObject,
    mut v_as_5612_: *mut leanh::LeanObject,
    mut v_i_5613_: usize,
    mut v_stop_5614_: usize,
    mut v_b_5615_: *mut leanh::LeanObject,
    mut v___y_5616_: *mut leanh::LeanObject,
    mut v___y_5617_: *mut leanh::LeanObject,
    mut v___y_5618_: *mut leanh::LeanObject,
    mut v___y_5619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___redArg(v_n_5610_, v_todo_5611_, v_as_5612_, v_i_5613_, v_stop_5614_, v_b_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
    return v___x_5621_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1___boxed(
    mut v_00_u03b1_5622_: *mut leanh::LeanObject,
    mut v_n_5623_: *mut leanh::LeanObject,
    mut v_todo_5624_: *mut leanh::LeanObject,
    mut v_as_5625_: *mut leanh::LeanObject,
    mut v_i_5626_: *mut leanh::LeanObject,
    mut v_stop_5627_: *mut leanh::LeanObject,
    mut v_b_5628_: *mut leanh::LeanObject,
    mut v___y_5629_: *mut leanh::LeanObject,
    mut v___y_5630_: *mut leanh::LeanObject,
    mut v___y_5631_: *mut leanh::LeanObject,
    mut v___y_5632_: *mut leanh::LeanObject,
    mut v___y_5633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5634_: usize = 0;
    let mut v_stop_boxed_5635_: usize = 0;
    let mut v_res_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5634_ = leanh::lean_unbox_usize(v_i_5626_);
    leanh::lean_dec(v_i_5626_);
    v_stop_boxed_5635_ = leanh::lean_unbox_usize(v_stop_5627_);
    leanh::lean_dec(v_stop_5627_);
    v_res_5636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process_spec__1(v_00_u03b1_5622_, v_n_5623_, v_todo_5624_, v_as_5625_, v_i_boxed_5634_, v_stop_boxed_5635_, v_b_5628_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_);
    leanh::lean_dec(v___y_5632_);
    leanh::lean_dec_ref(v___y_5631_);
    leanh::lean_dec(v___y_5630_);
    leanh::lean_dec_ref(v___y_5629_);
    leanh::lean_dec_ref(v_as_5625_);
    leanh::lean_dec(v_n_5623_);
    return v_res_5636_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(
    mut v_result_5637_: *mut leanh::LeanObject,
    mut v_k_5638_: *mut leanh::LeanObject,
    mut v_c_5639_: *mut leanh::LeanObject,
    mut v___y_5640_: *mut leanh::LeanObject,
    mut v___y_5641_: *mut leanh::LeanObject,
    mut v___y_5642_: *mut leanh::LeanObject,
    mut v___y_5643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5645_ = l_Lean_Meta_DiscrTree_Key_arity(v_k_5638_);
    v___x_5646_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs___closed__0;
    v___x_5647_ =
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(
            v___x_5645_,
            v___x_5646_,
            v_c_5639_,
            v_result_5637_,
            v___y_5640_,
            v___y_5641_,
            v___y_5642_,
            v___y_5643_,
        );
    return v___x_5647_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0___boxed(
    mut v_result_5648_: *mut leanh::LeanObject,
    mut v_k_5649_: *mut leanh::LeanObject,
    mut v_c_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
    mut v___y_5653_: *mut leanh::LeanObject,
    mut v___y_5654_: *mut leanh::LeanObject,
    mut v___y_5655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5656_ = l_Lean_Meta_DiscrTree_getUnify___redArg___lam__0(
        v_result_5648_,
        v_k_5649_,
        v_c_5650_,
        v___y_5651_,
        v___y_5652_,
        v___y_5653_,
        v___y_5654_,
    );
    leanh::lean_dec(v___y_5654_);
    leanh::lean_dec_ref(v___y_5653_);
    leanh::lean_dec(v___y_5652_);
    leanh::lean_dec_ref(v___y_5651_);
    leanh::lean_dec(v_k_5649_);
    return v_res_5656_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(
    mut v_f_5657_: *mut leanh::LeanObject,
    mut v_keys_5658_: *mut leanh::LeanObject,
    mut v_vals_5659_: *mut leanh::LeanObject,
    mut v_i_5660_: *mut leanh::LeanObject,
    mut v_acc_5661_: *mut leanh::LeanObject,
    mut v___y_5662_: *mut leanh::LeanObject,
    mut v___y_5663_: *mut leanh::LeanObject,
    mut v___y_5664_: *mut leanh::LeanObject,
    mut v___y_5665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5667_ = lean_array_get_size(v_keys_5658_);
                v___x_5668_ = lean_nat_dec_lt(v_i_5660_, v___x_5667_);
                if v___x_5668_ == 0 {
                    leanh::lean_dec(v_i_5660_);
                    leanh::lean_dec_ref(v_f_5657_);
                    v___x_5669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5669_, 0, v_acc_5661_);
                    return v___x_5669_;
                } else {
                    v_k_5670_ = lean_array_fget_borrowed(v_keys_5658_, v_i_5660_);
                    v_v_5671_ = lean_array_fget_borrowed(v_vals_5659_, v_i_5660_);
                    leanh::lean_inc_ref(v_f_5657_);
                    leanh::lean_inc(v___y_5665_);
                    leanh::lean_inc_ref(v___y_5664_);
                    leanh::lean_inc(v___y_5663_);
                    leanh::lean_inc_ref(v___y_5662_);
                    leanh::lean_inc(v_v_5671_);
                    leanh::lean_inc(v_k_5670_);
                    v___x_5672_ = leanh::lean_apply_8(
                        v_f_5657_,
                        v_acc_5661_,
                        v_k_5670_,
                        v_v_5671_,
                        v___y_5662_,
                        v___y_5663_,
                        v___y_5664_,
                        v___y_5665_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_5672_) == 0 {
                        v_a_5673_ = leanh::lean_ctor_get(v___x_5672_, 0);
                        leanh::lean_inc(v_a_5673_);
                        leanh::lean_dec_ref_known(v___x_5672_, 1);
                        v___x_5674_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5675_ = lean_nat_add(v_i_5660_, v___x_5674_);
                        leanh::lean_dec(v_i_5660_);
                        v_i_5660_ = v___x_5675_;
                        v_acc_5661_ = v_a_5673_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_5660_);
                        leanh::lean_dec_ref(v_f_5657_);
                        return v___x_5672_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_f_5677_: *mut leanh::LeanObject,
    mut v_keys_5678_: *mut leanh::LeanObject,
    mut v_vals_5679_: *mut leanh::LeanObject,
    mut v_i_5680_: *mut leanh::LeanObject,
    mut v_acc_5681_: *mut leanh::LeanObject,
    mut v___y_5682_: *mut leanh::LeanObject,
    mut v___y_5683_: *mut leanh::LeanObject,
    mut v___y_5684_: *mut leanh::LeanObject,
    mut v___y_5685_: *mut leanh::LeanObject,
    mut v___y_5686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5687_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_5677_, v_keys_5678_, v_vals_5679_, v_i_5680_, v_acc_5681_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
    leanh::lean_dec(v___y_5685_);
    leanh::lean_dec_ref(v___y_5684_);
    leanh::lean_dec(v___y_5683_);
    leanh::lean_dec_ref(v___y_5682_);
    leanh::lean_dec_ref(v_vals_5679_);
    leanh::lean_dec_ref(v_keys_5678_);
    return v_res_5687_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(
    mut v_f_5688_: *mut leanh::LeanObject,
    mut v_x_5689_: *mut leanh::LeanObject,
    mut v_x_5690_: *mut leanh::LeanObject,
    mut v___y_5691_: *mut leanh::LeanObject,
    mut v___y_5692_: *mut leanh::LeanObject,
    mut v___y_5693_: *mut leanh::LeanObject,
    mut v___y_5694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: u8 = 0;
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: usize = 0;
    let mut v___x_5711_: usize = 0;
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: usize = 0;
    let mut v___x_5714_: usize = 0;
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut v_ks_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5689_) == 0 {
                    v_es_5696_ = leanh::lean_ctor_get(v_x_5689_, 0);
                    v_isSharedCheck_5716_ = (!leanh::lean_is_exclusive(v_x_5689_)) as u8;
                    if v_isSharedCheck_5716_ == 0 {
                        v___x_5698_ = v_x_5689_;
                        v_isShared_5699_ = v_isSharedCheck_5716_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_5696_);
                        leanh::lean_dec(v_x_5689_);
                        v___x_5698_ = leanh::lean_box(0);
                        v_isShared_5699_ = v_isSharedCheck_5716_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_5717_ = leanh::lean_ctor_get(v_x_5689_, 0);
                    leanh::lean_inc_ref(v_ks_5717_);
                    v_vs_5718_ = leanh::lean_ctor_get(v_x_5689_, 1);
                    leanh::lean_inc_ref(v_vs_5718_);
                    leanh::lean_dec_ref_known(v_x_5689_, 2);
                    v___x_5719_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_5688_, v_ks_5717_, v_vs_5718_, v___x_5719_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
                    leanh::lean_dec_ref(v_vs_5718_);
                    leanh::lean_dec_ref(v_ks_5717_);
                    return v___x_5720_;
                }
            }
            1 => {
                v___x_5700_ = leanh::lean_unsigned_to_nat(0);
                v___x_5701_ = lean_array_get_size(v_es_5696_);
                v___x_5702_ = lean_nat_dec_lt(v___x_5700_, v___x_5701_);
                if v___x_5702_ == 0 {
                    leanh::lean_dec_ref(v_es_5696_);
                    leanh::lean_dec_ref(v_f_5688_);
                    if v_isShared_5699_ == 0 {
                        leanh::lean_ctor_set(v___x_5698_, 0, v_x_5690_);
                        v___x_5704_ = v___x_5698_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5705_, 0, v_x_5690_);
                        v___x_5704_ = v_reuseFailAlloc_5705_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5706_ = lean_nat_dec_le(v___x_5701_, v___x_5701_);
                    if v___x_5706_ == 0 {
                        if v___x_5702_ == 0 {
                            leanh::lean_dec_ref(v_es_5696_);
                            leanh::lean_dec_ref(v_f_5688_);
                            if v_isShared_5699_ == 0 {
                                leanh::lean_ctor_set(v___x_5698_, 0, v_x_5690_);
                                v___x_5708_ = v___x_5698_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5709_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5709_, 0, v_x_5690_);
                                v___x_5708_ = v_reuseFailAlloc_5709_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_5698_);
                            v___x_5710_ = 0usize;
                            v___x_5711_ = lean_usize_of_nat(v___x_5701_);
                            v___x_5712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_5688_, v_es_5696_, v___x_5710_, v___x_5711_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
                            leanh::lean_dec_ref(v_es_5696_);
                            return v___x_5712_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5698_);
                        v___x_5713_ = 0usize;
                        v___x_5714_ = lean_usize_of_nat(v___x_5701_);
                        v___x_5715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_5688_, v_es_5696_, v___x_5713_, v___x_5714_, v_x_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
                        leanh::lean_dec_ref(v_es_5696_);
                        return v___x_5715_;
                    }
                }
            }
            2 => {
                return v___x_5704_;
            }
            3 => {
                return v___x_5708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(
    mut v_f_5721_: *mut leanh::LeanObject,
    mut v_as_5722_: *mut leanh::LeanObject,
    mut v_i_5723_: usize,
    mut v_stop_5724_: usize,
    mut v_b_5725_: *mut leanh::LeanObject,
    mut v___y_5726_: *mut leanh::LeanObject,
    mut v___y_5727_: *mut leanh::LeanObject,
    mut v___y_5728_: *mut leanh::LeanObject,
    mut v___y_5729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: usize = 0;
    let mut v___x_5734_: usize = 0;
    let mut v___y_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: u8 = 0;
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5739_ = lean_usize_dec_eq(v_i_5723_, v_stop_5724_);
                if v___x_5739_ == 0 {
                    v___x_5740_ = lean_array_uget_borrowed(v_as_5722_, v_i_5723_);
                    match leanh::lean_obj_tag(v___x_5740_) {
                        0 => {
                            v_key_5741_ = leanh::lean_ctor_get(v___x_5740_, 0);
                            v_val_5742_ = leanh::lean_ctor_get(v___x_5740_, 1);
                            leanh::lean_inc_ref(v_f_5721_);
                            leanh::lean_inc(v___y_5729_);
                            leanh::lean_inc_ref(v___y_5728_);
                            leanh::lean_inc(v___y_5727_);
                            leanh::lean_inc_ref(v___y_5726_);
                            leanh::lean_inc(v_val_5742_);
                            leanh::lean_inc(v_key_5741_);
                            v___x_5743_ = leanh::lean_apply_8(
                                v_f_5721_,
                                v_b_5725_,
                                v_key_5741_,
                                v_val_5742_,
                                v___y_5726_,
                                v___y_5727_,
                                v___y_5728_,
                                v___y_5729_,
                                leanh::lean_box(0),
                            );
                            v___y_5737_ = v___x_5743_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_5744_ = leanh::lean_ctor_get(v___x_5740_, 0);
                            leanh::lean_inc(v_node_5744_);
                            leanh::lean_inc_ref(v_f_5721_);
                            v___x_5745_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_5721_, v_node_5744_, v_b_5725_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_);
                            v___y_5737_ = v___x_5745_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_5732_ = v_b_5725_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_5721_);
                    v___x_5746_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5746_, 0, v_b_5725_);
                    return v___x_5746_;
                }
            }
            1 => {
                v___x_5733_ = 1usize;
                v___x_5734_ = lean_usize_add(v_i_5723_, v___x_5733_);
                v_i_5723_ = v___x_5734_;
                v_b_5725_ = v_a_5732_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_5737_) == 0 {
                    v_a_5738_ = leanh::lean_ctor_get(v___y_5737_, 0);
                    leanh::lean_inc(v_a_5738_);
                    leanh::lean_dec_ref_known(v___y_5737_, 1);
                    v_a_5732_ = v_a_5738_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_f_5721_);
                    return v___y_5737_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_5747_: *mut leanh::LeanObject,
    mut v_as_5748_: *mut leanh::LeanObject,
    mut v_i_5749_: *mut leanh::LeanObject,
    mut v_stop_5750_: *mut leanh::LeanObject,
    mut v_b_5751_: *mut leanh::LeanObject,
    mut v___y_5752_: *mut leanh::LeanObject,
    mut v___y_5753_: *mut leanh::LeanObject,
    mut v___y_5754_: *mut leanh::LeanObject,
    mut v___y_5755_: *mut leanh::LeanObject,
    mut v___y_5756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5757_: usize = 0;
    let mut v_stop_boxed_5758_: usize = 0;
    let mut v_res_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5757_ = leanh::lean_unbox_usize(v_i_5749_);
    leanh::lean_dec(v_i_5749_);
    v_stop_boxed_5758_ = leanh::lean_unbox_usize(v_stop_5750_);
    leanh::lean_dec(v_stop_5750_);
    v_res_5759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_5747_, v_as_5748_, v_i_boxed_5757_, v_stop_boxed_5758_, v_b_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_);
    leanh::lean_dec(v___y_5755_);
    leanh::lean_dec_ref(v___y_5754_);
    leanh::lean_dec(v___y_5753_);
    leanh::lean_dec_ref(v___y_5752_);
    leanh::lean_dec_ref(v_as_5748_);
    return v_res_5759_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg___boxed(
    mut v_f_5760_: *mut leanh::LeanObject,
    mut v_x_5761_: *mut leanh::LeanObject,
    mut v_x_5762_: *mut leanh::LeanObject,
    mut v___y_5763_: *mut leanh::LeanObject,
    mut v___y_5764_: *mut leanh::LeanObject,
    mut v___y_5765_: *mut leanh::LeanObject,
    mut v___y_5766_: *mut leanh::LeanObject,
    mut v___y_5767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5768_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_5760_, v_x_5761_, v_x_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_);
    leanh::lean_dec(v___y_5766_);
    leanh::lean_dec_ref(v___y_5765_);
    leanh::lean_dec(v___y_5764_);
    leanh::lean_dec_ref(v___y_5763_);
    return v_res_5768_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getUnify___redArg(
    mut v_d_5770_: *mut leanh::LeanObject,
    mut v_e_5771_: *mut leanh::LeanObject,
    mut v_a_5772_: *mut leanh::LeanObject,
    mut v_a_5773_: *mut leanh::LeanObject,
    mut v_a_5774_: *mut leanh::LeanObject,
    mut v_a_5775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5778_: u8 = 0;
    let mut v_ctxApprox_5779_: u8 = 0;
    let mut v_quasiPatternApprox_5780_: u8 = 0;
    let mut v_constApprox_5781_: u8 = 0;
    let mut v_isDefEqStuckEx_5782_: u8 = 0;
    let mut v_unificationHints_5783_: u8 = 0;
    let mut v_proofIrrelevance_5784_: u8 = 0;
    let mut v_assignSyntheticOpaque_5785_: u8 = 0;
    let mut v_offsetCnstrs_5786_: u8 = 0;
    let mut v_etaStruct_5787_: u8 = 0;
    let mut v_univApprox_5788_: u8 = 0;
    let mut v_iota_5789_: u8 = 0;
    let mut v_beta_5790_: u8 = 0;
    let mut v_proj_5791_: u8 = 0;
    let mut v_zeta_5792_: u8 = 0;
    let mut v_zetaDelta_5793_: u8 = 0;
    let mut v_zetaUnused_5794_: u8 = 0;
    let mut v_zetaHave_5795_: u8 = 0;
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5798_: u8 = 0;
    let mut v_trackZetaDelta_5799_: u8 = 0;
    let mut v_zetaDeltaSet_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5806_: u8 = 0;
    let mut v_inTypeClassResolution_5807_: u8 = 0;
    let mut v_cacheInferType_5808_: u8 = 0;
    let mut v___x_5809_: u8 = 0;
    let mut v_config_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: u64 = 0;
    let mut v___x_5813_: u64 = 0;
    let mut v___x_5814_: u64 = 0;
    let mut v___x_5815_: u8 = 0;
    let mut v___x_5816_: u64 = 0;
    let mut v___x_5817_: u64 = 0;
    let mut v_key_5818_: u64 = 0;
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: u8 = 0;
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5826_: u8 = 0;
    let mut v_fst_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5840_: u8 = 0;
    let mut v_a_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5844_: u8 = 0;
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5848_: u8 = 0;
    let mut v_reuseFailAlloc_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5777_ = l_Lean_Meta_Context_config(v_a_5772_);
                v_foApprox_5778_ = leanh::lean_ctor_get_uint8(v___x_5777_, 0 as u32);
                v_ctxApprox_5779_ = leanh::lean_ctor_get_uint8(v___x_5777_, 1 as u32);
                v_quasiPatternApprox_5780_ =
                    leanh::lean_ctor_get_uint8(v___x_5777_, 2 as u32);
                v_constApprox_5781_ = leanh::lean_ctor_get_uint8(v___x_5777_, 3 as u32);
                v_isDefEqStuckEx_5782_ = leanh::lean_ctor_get_uint8(v___x_5777_, 4 as u32);
                v_unificationHints_5783_ = leanh::lean_ctor_get_uint8(v___x_5777_, 5 as u32);
                v_proofIrrelevance_5784_ = leanh::lean_ctor_get_uint8(v___x_5777_, 6 as u32);
                v_assignSyntheticOpaque_5785_ =
                    leanh::lean_ctor_get_uint8(v___x_5777_, 7 as u32);
                v_offsetCnstrs_5786_ = leanh::lean_ctor_get_uint8(v___x_5777_, 8 as u32);
                v_etaStruct_5787_ = leanh::lean_ctor_get_uint8(v___x_5777_, 10 as u32);
                v_univApprox_5788_ = leanh::lean_ctor_get_uint8(v___x_5777_, 11 as u32);
                v_iota_5789_ = leanh::lean_ctor_get_uint8(v___x_5777_, 12 as u32);
                v_beta_5790_ = leanh::lean_ctor_get_uint8(v___x_5777_, 13 as u32);
                v_proj_5791_ = leanh::lean_ctor_get_uint8(v___x_5777_, 14 as u32);
                v_zeta_5792_ = leanh::lean_ctor_get_uint8(v___x_5777_, 15 as u32);
                v_zetaDelta_5793_ = leanh::lean_ctor_get_uint8(v___x_5777_, 16 as u32);
                v_zetaUnused_5794_ = leanh::lean_ctor_get_uint8(v___x_5777_, 17 as u32);
                v_zetaHave_5795_ = leanh::lean_ctor_get_uint8(v___x_5777_, 18 as u32);
                v_isSharedCheck_5850_ = (!leanh::lean_is_exclusive(v___x_5777_)) as u8;
                if v_isSharedCheck_5850_ == 0 {
                    v___x_5797_ = v___x_5777_;
                    v_isShared_5798_ = v_isSharedCheck_5850_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5777_);
                    v___x_5797_ = leanh::lean_box(0);
                    v_isShared_5798_ = v_isSharedCheck_5850_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_5799_ = leanh::lean_ctor_get_uint8(
                    v_a_5772_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5800_ = leanh::lean_ctor_get(v_a_5772_, 1);
                v_lctx_5801_ = leanh::lean_ctor_get(v_a_5772_, 2);
                v_localInstances_5802_ = leanh::lean_ctor_get(v_a_5772_, 3);
                v_defEqCtx_x3f_5803_ = leanh::lean_ctor_get(v_a_5772_, 4);
                v_synthPendingDepth_5804_ = leanh::lean_ctor_get(v_a_5772_, 5);
                v_canUnfold_x3f_5805_ = leanh::lean_ctor_get(v_a_5772_, 6);
                v_univApprox_5806_ = leanh::lean_ctor_get_uint8(
                    v_a_5772_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5807_ = leanh::lean_ctor_get_uint8(
                    v_a_5772_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5808_ = leanh::lean_ctor_get_uint8(
                    v_a_5772_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5809_ = 2;
                if v_isShared_5798_ == 0 {
                    v_config_5811_ = v___x_5797_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5849_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        0 as u32,
                        v_foApprox_5778_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        1 as u32,
                        v_ctxApprox_5779_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        2 as u32,
                        v_quasiPatternApprox_5780_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        3 as u32,
                        v_constApprox_5781_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        4 as u32,
                        v_isDefEqStuckEx_5782_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        5 as u32,
                        v_unificationHints_5783_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        6 as u32,
                        v_proofIrrelevance_5784_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        7 as u32,
                        v_assignSyntheticOpaque_5785_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        8 as u32,
                        v_offsetCnstrs_5786_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        10 as u32,
                        v_etaStruct_5787_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        11 as u32,
                        v_univApprox_5788_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        12 as u32,
                        v_iota_5789_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        13 as u32,
                        v_beta_5790_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        14 as u32,
                        v_proj_5791_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        15 as u32,
                        v_zeta_5792_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        16 as u32,
                        v_zetaDelta_5793_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        17 as u32,
                        v_zetaUnused_5794_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5849_,
                        18 as u32,
                        v_zetaHave_5795_,
                    );
                    v_config_5811_ = v_reuseFailAlloc_5849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_5811_, 9 as u32, v___x_5809_);
                v___x_5812_ = l_Lean_Meta_Context_configKey(v_a_5772_);
                v___x_5813_ = 3u64;
                v___x_5814_ = lean_uint64_shift_right(v___x_5812_, v___x_5813_);
                v___x_5815_ = 1;
                v___x_5816_ = lean_uint64_shift_left(v___x_5814_, v___x_5813_);
                v___x_5817_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_mkPath___closed__0_once),
                    _init_l_Lean_Meta_DiscrTree_mkPath___closed__0,
                );
                v_key_5818_ = lean_uint64_lor(v___x_5816_, v___x_5817_);
                v___x_5819_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_5819_, 0, v_config_5811_);
                leanh::lean_ctor_set_uint64(
                    v___x_5819_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_5818_,
                );
                leanh::lean_inc(v_canUnfold_x3f_5805_);
                leanh::lean_inc(v_synthPendingDepth_5804_);
                leanh::lean_inc(v_defEqCtx_x3f_5803_);
                leanh::lean_inc_ref(v_localInstances_5802_);
                leanh::lean_inc_ref(v_lctx_5801_);
                leanh::lean_inc(v_zetaDeltaSet_5800_);
                v___x_5820_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_5820_, 0, v___x_5819_);
                leanh::lean_ctor_set(v___x_5820_, 1, v_zetaDeltaSet_5800_);
                leanh::lean_ctor_set(v___x_5820_, 2, v_lctx_5801_);
                leanh::lean_ctor_set(v___x_5820_, 3, v_localInstances_5802_);
                leanh::lean_ctor_set(v___x_5820_, 4, v_defEqCtx_x3f_5803_);
                leanh::lean_ctor_set(v___x_5820_, 5, v_synthPendingDepth_5804_);
                leanh::lean_ctor_set(v___x_5820_, 6, v_canUnfold_x3f_5805_);
                leanh::lean_ctor_set_uint8(
                    v___x_5820_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5799_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5820_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5806_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5820_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5807_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5820_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5808_,
                );
                v___x_5821_ = 0;
                v___x_5822_ =
                    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getKeyArgs(
                        v_e_5771_,
                        v___x_5821_,
                        v___x_5815_,
                        v___x_5820_,
                        v_a_5773_,
                        v_a_5774_,
                        v_a_5775_,
                    );
                if leanh::lean_obj_tag(v___x_5822_) == 0 {
                    v_a_5823_ = leanh::lean_ctor_get(v___x_5822_, 0);
                    v_isSharedCheck_5840_ = (!leanh::lean_is_exclusive(v___x_5822_)) as u8;
                    if v_isSharedCheck_5840_ == 0 {
                        v___x_5825_ = v___x_5822_;
                        v_isShared_5826_ = v_isSharedCheck_5840_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5823_);
                        leanh::lean_dec(v___x_5822_);
                        v___x_5825_ = leanh::lean_box(0);
                        v_isShared_5826_ = v_isSharedCheck_5840_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_5820_, 7);
                    leanh::lean_dec_ref(v_d_5770_);
                    v_a_5841_ = leanh::lean_ctor_get(v___x_5822_, 0);
                    v_isSharedCheck_5848_ = (!leanh::lean_is_exclusive(v___x_5822_)) as u8;
                    if v_isSharedCheck_5848_ == 0 {
                        v___x_5843_ = v___x_5822_;
                        v_isShared_5844_ = v_isSharedCheck_5848_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5841_);
                        leanh::lean_dec(v___x_5822_);
                        v___x_5843_ = leanh::lean_box(0);
                        v_isShared_5844_ = v_isSharedCheck_5848_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_5827_ = leanh::lean_ctor_get(v_a_5823_, 0);
                leanh::lean_inc(v_fst_5827_);
                if leanh::lean_obj_tag(v_fst_5827_) == 0 {
                    leanh::lean_del_object(v___x_5825_);
                    leanh::lean_dec(v_a_5823_);
                    v___f_5828_ = l_Lean_Meta_DiscrTree_getUnify___redArg___closed__0;
                    v___x_5829_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_findKey___redArg___closed__1;
                    v___x_5830_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v___f_5828_, v_d_5770_, v___x_5829_, v___x_5820_, v_a_5773_, v_a_5774_, v_a_5775_);
                    leanh::lean_dec_ref_known(v___x_5820_, 7);
                    return v___x_5830_;
                } else {
                    v_snd_5831_ = leanh::lean_ctor_get(v_a_5823_, 1);
                    leanh::lean_inc(v_snd_5831_);
                    leanh::lean_dec(v_a_5823_);
                    v___x_5832_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult___redArg(v_d_5770_);
                    v___x_5833_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getStarResult_spec__0___redArg(v_d_5770_, v_fst_5827_);
                    leanh::lean_dec(v_fst_5827_);
                    leanh::lean_dec_ref(v_d_5770_);
                    if leanh::lean_obj_tag(v___x_5833_) == 0 {
                        leanh::lean_dec(v_snd_5831_);
                        leanh::lean_dec_ref_known(v___x_5820_, 7);
                        if v_isShared_5826_ == 0 {
                            leanh::lean_ctor_set(v___x_5825_, 0, v___x_5832_);
                            v___x_5835_ = v___x_5825_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5836_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 0, v___x_5832_);
                            v___x_5835_ = v_reuseFailAlloc_5836_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5825_);
                        v_val_5837_ = leanh::lean_ctor_get(v___x_5833_, 0);
                        leanh::lean_inc(v_val_5837_);
                        leanh::lean_dec_ref_known(v___x_5833_, 1);
                        v___x_5838_ = leanh::lean_unsigned_to_nat(0);
                        v___x_5839_ = l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_getUnify_process___redArg(v___x_5838_, v_snd_5831_, v_val_5837_, v___x_5832_, v___x_5820_, v_a_5773_, v_a_5774_, v_a_5775_);
                        leanh::lean_dec_ref_known(v___x_5820_, 7);
                        return v___x_5839_;
                    }
                }
            }
            4 => {
                return v___x_5835_;
            }
            5 => {
                if v_isShared_5844_ == 0 {
                    v___x_5846_ = v___x_5843_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_a_5841_);
                    v___x_5846_ = v_reuseFailAlloc_5847_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5846_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_getUnify___redArg___boxed(
    mut v_d_5851_: *mut leanh::LeanObject,
    mut v_e_5852_: *mut leanh::LeanObject,
    mut v_a_5853_: *mut leanh::LeanObject,
    mut v_a_5854_: *mut leanh::LeanObject,
    mut v_a_5855_: *mut leanh::LeanObject,
    mut v_a_5856_: *mut leanh::LeanObject,
    mut v_a_5857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_Meta_DiscrTree_getUnify___redArg(
        v_d_5851_, v_e_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_,
    );
    leanh::lean_dec(v_a_5856_);
    leanh::lean_dec_ref(v_a_5855_);
    leanh::lean_dec(v_a_5854_);
    leanh::lean_dec_ref(v_a_5853_);
    return v_res_5858_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getUnify(
    mut v_00_u03b1_5859_: *mut leanh::LeanObject,
    mut v_d_5860_: *mut leanh::LeanObject,
    mut v_e_5861_: *mut leanh::LeanObject,
    mut v_a_5862_: *mut leanh::LeanObject,
    mut v_a_5863_: *mut leanh::LeanObject,
    mut v_a_5864_: *mut leanh::LeanObject,
    mut v_a_5865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5867_ = l_Lean_Meta_DiscrTree_getUnify___redArg(
        v_d_5860_, v_e_5861_, v_a_5862_, v_a_5863_, v_a_5864_, v_a_5865_,
    );
    return v___x_5867_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_getUnify___boxed(
    mut v_00_u03b1_5868_: *mut leanh::LeanObject,
    mut v_d_5869_: *mut leanh::LeanObject,
    mut v_e_5870_: *mut leanh::LeanObject,
    mut v_a_5871_: *mut leanh::LeanObject,
    mut v_a_5872_: *mut leanh::LeanObject,
    mut v_a_5873_: *mut leanh::LeanObject,
    mut v_a_5874_: *mut leanh::LeanObject,
    mut v_a_5875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5876_ = l_Lean_Meta_DiscrTree_getUnify(
        v_00_u03b1_5868_,
        v_d_5869_,
        v_e_5870_,
        v_a_5871_,
        v_a_5872_,
        v_a_5873_,
        v_a_5874_,
    );
    leanh::lean_dec(v_a_5874_);
    leanh::lean_dec_ref(v_a_5873_);
    leanh::lean_dec(v_a_5872_);
    leanh::lean_dec_ref(v_a_5871_);
    return v_res_5876_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(
    mut v_map_5877_: *mut leanh::LeanObject,
    mut v_f_5878_: *mut leanh::LeanObject,
    mut v_init_5879_: *mut leanh::LeanObject,
    mut v___y_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5885_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_5878_, v_map_5877_, v_init_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_);
    return v___x_5885_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg___boxed(
    mut v_map_5886_: *mut leanh::LeanObject,
    mut v_f_5887_: *mut leanh::LeanObject,
    mut v_init_5888_: *mut leanh::LeanObject,
    mut v___y_5889_: *mut leanh::LeanObject,
    mut v___y_5890_: *mut leanh::LeanObject,
    mut v___y_5891_: *mut leanh::LeanObject,
    mut v___y_5892_: *mut leanh::LeanObject,
    mut v___y_5893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5894_ =
        l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___redArg(
            v_map_5886_,
            v_f_5887_,
            v_init_5888_,
            v___y_5889_,
            v___y_5890_,
            v___y_5891_,
            v___y_5892_,
        );
    leanh::lean_dec(v___y_5892_);
    leanh::lean_dec_ref(v___y_5891_);
    leanh::lean_dec(v___y_5890_);
    leanh::lean_dec_ref(v___y_5889_);
    return v_res_5894_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(
    mut v_00_u03c3_5895_: *mut leanh::LeanObject,
    mut v_00_u03b2_5896_: *mut leanh::LeanObject,
    mut v_map_5897_: *mut leanh::LeanObject,
    mut v_f_5898_: *mut leanh::LeanObject,
    mut v_init_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
    mut v___y_5902_: *mut leanh::LeanObject,
    mut v___y_5903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5905_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_5898_, v_map_5897_, v_init_5899_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_);
    return v___x_5905_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0___boxed(
    mut v_00_u03c3_5906_: *mut leanh::LeanObject,
    mut v_00_u03b2_5907_: *mut leanh::LeanObject,
    mut v_map_5908_: *mut leanh::LeanObject,
    mut v_f_5909_: *mut leanh::LeanObject,
    mut v_init_5910_: *mut leanh::LeanObject,
    mut v___y_5911_: *mut leanh::LeanObject,
    mut v___y_5912_: *mut leanh::LeanObject,
    mut v___y_5913_: *mut leanh::LeanObject,
    mut v___y_5914_: *mut leanh::LeanObject,
    mut v___y_5915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5916_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0(
        v_00_u03c3_5906_,
        v_00_u03b2_5907_,
        v_map_5908_,
        v_f_5909_,
        v_init_5910_,
        v___y_5911_,
        v___y_5912_,
        v___y_5913_,
        v___y_5914_,
    );
    leanh::lean_dec(v___y_5914_);
    leanh::lean_dec_ref(v___y_5913_);
    leanh::lean_dec(v___y_5912_);
    leanh::lean_dec_ref(v___y_5911_);
    return v_res_5916_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(
    mut v_00_u03c3_5917_: *mut leanh::LeanObject,
    mut v_00_u03b1_5918_: *mut leanh::LeanObject,
    mut v_00_u03b2_5919_: *mut leanh::LeanObject,
    mut v_f_5920_: *mut leanh::LeanObject,
    mut v_x_5921_: *mut leanh::LeanObject,
    mut v_x_5922_: *mut leanh::LeanObject,
    mut v___y_5923_: *mut leanh::LeanObject,
    mut v___y_5924_: *mut leanh::LeanObject,
    mut v___y_5925_: *mut leanh::LeanObject,
    mut v___y_5926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5928_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___redArg(v_f_5920_, v_x_5921_, v_x_5922_, v___y_5923_, v___y_5924_, v___y_5925_, v___y_5926_);
    return v___x_5928_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0___boxed(
    mut v_00_u03c3_5929_: *mut leanh::LeanObject,
    mut v_00_u03b1_5930_: *mut leanh::LeanObject,
    mut v_00_u03b2_5931_: *mut leanh::LeanObject,
    mut v_f_5932_: *mut leanh::LeanObject,
    mut v_x_5933_: *mut leanh::LeanObject,
    mut v_x_5934_: *mut leanh::LeanObject,
    mut v___y_5935_: *mut leanh::LeanObject,
    mut v___y_5936_: *mut leanh::LeanObject,
    mut v___y_5937_: *mut leanh::LeanObject,
    mut v___y_5938_: *mut leanh::LeanObject,
    mut v___y_5939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5940_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0(v_00_u03c3_5929_, v_00_u03b1_5930_, v_00_u03b2_5931_, v_f_5932_, v_x_5933_, v_x_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
    leanh::lean_dec(v___y_5938_);
    leanh::lean_dec_ref(v___y_5937_);
    leanh::lean_dec(v___y_5936_);
    leanh::lean_dec_ref(v___y_5935_);
    return v_res_5940_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(
    mut v_00_u03b1_5941_: *mut leanh::LeanObject,
    mut v_00_u03b2_5942_: *mut leanh::LeanObject,
    mut v_00_u03c3_5943_: *mut leanh::LeanObject,
    mut v_f_5944_: *mut leanh::LeanObject,
    mut v_as_5945_: *mut leanh::LeanObject,
    mut v_i_5946_: usize,
    mut v_stop_5947_: usize,
    mut v_b_5948_: *mut leanh::LeanObject,
    mut v___y_5949_: *mut leanh::LeanObject,
    mut v___y_5950_: *mut leanh::LeanObject,
    mut v___y_5951_: *mut leanh::LeanObject,
    mut v___y_5952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___redArg(v_f_5944_, v_as_5945_, v_i_5946_, v_stop_5947_, v_b_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
    return v___x_5954_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_5955_: *mut leanh::LeanObject,
    mut v_00_u03b2_5956_: *mut leanh::LeanObject,
    mut v_00_u03c3_5957_: *mut leanh::LeanObject,
    mut v_f_5958_: *mut leanh::LeanObject,
    mut v_as_5959_: *mut leanh::LeanObject,
    mut v_i_5960_: *mut leanh::LeanObject,
    mut v_stop_5961_: *mut leanh::LeanObject,
    mut v_b_5962_: *mut leanh::LeanObject,
    mut v___y_5963_: *mut leanh::LeanObject,
    mut v___y_5964_: *mut leanh::LeanObject,
    mut v___y_5965_: *mut leanh::LeanObject,
    mut v___y_5966_: *mut leanh::LeanObject,
    mut v___y_5967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5968_: usize = 0;
    let mut v_stop_boxed_5969_: usize = 0;
    let mut v_res_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5968_ = leanh::lean_unbox_usize(v_i_5960_);
    leanh::lean_dec(v_i_5960_);
    v_stop_boxed_5969_ = leanh::lean_unbox_usize(v_stop_5961_);
    leanh::lean_dec(v_stop_5961_);
    v_res_5970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__1(v_00_u03b1_5955_, v_00_u03b2_5956_, v_00_u03c3_5957_, v_f_5958_, v_as_5959_, v_i_boxed_5968_, v_stop_boxed_5969_, v_b_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
    leanh::lean_dec(v___y_5966_);
    leanh::lean_dec_ref(v___y_5965_);
    leanh::lean_dec(v___y_5964_);
    leanh::lean_dec_ref(v___y_5963_);
    leanh::lean_dec_ref(v_as_5959_);
    return v_res_5970_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(
    mut v_00_u03c3_5971_: *mut leanh::LeanObject,
    mut v_00_u03b1_5972_: *mut leanh::LeanObject,
    mut v_00_u03b2_5973_: *mut leanh::LeanObject,
    mut v_f_5974_: *mut leanh::LeanObject,
    mut v_keys_5975_: *mut leanh::LeanObject,
    mut v_vals_5976_: *mut leanh::LeanObject,
    mut v_heq_5977_: *mut leanh::LeanObject,
    mut v_i_5978_: *mut leanh::LeanObject,
    mut v_acc_5979_: *mut leanh::LeanObject,
    mut v___y_5980_: *mut leanh::LeanObject,
    mut v___y_5981_: *mut leanh::LeanObject,
    mut v___y_5982_: *mut leanh::LeanObject,
    mut v___y_5983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5985_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___redArg(v_f_5974_, v_keys_5975_, v_vals_5976_, v_i_5978_, v_acc_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
    return v___x_5985_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03c3_5986_: *mut leanh::LeanObject,
    mut v_00_u03b1_5987_: *mut leanh::LeanObject,
    mut v_00_u03b2_5988_: *mut leanh::LeanObject,
    mut v_f_5989_: *mut leanh::LeanObject,
    mut v_keys_5990_: *mut leanh::LeanObject,
    mut v_vals_5991_: *mut leanh::LeanObject,
    mut v_heq_5992_: *mut leanh::LeanObject,
    mut v_i_5993_: *mut leanh::LeanObject,
    mut v_acc_5994_: *mut leanh::LeanObject,
    mut v___y_5995_: *mut leanh::LeanObject,
    mut v___y_5996_: *mut leanh::LeanObject,
    mut v___y_5997_: *mut leanh::LeanObject,
    mut v___y_5998_: *mut leanh::LeanObject,
    mut v___y_5999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6000_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_Meta_DiscrTree_getUnify_spec__0_spec__0_spec__2(v_00_u03c3_5986_, v_00_u03b1_5987_, v_00_u03b2_5988_, v_f_5989_, v_keys_5990_, v_vals_5991_, v_heq_5992_, v_i_5993_, v_acc_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_);
    leanh::lean_dec(v___y_5998_);
    leanh::lean_dec_ref(v___y_5997_);
    leanh::lean_dec(v___y_5996_);
    leanh::lean_dec_ref(v___y_5995_);
    leanh::lean_dec_ref(v_vals_5991_);
    leanh::lean_dec_ref(v_keys_5990_);
    return v_res_6000_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_DiscrTree_Main(
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
    res = runtime_initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar =
        _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_tmpStar,
    );
    l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity =
        _init_l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_DiscrTree_Main_0__Lean_Meta_DiscrTree_initCapacity,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_DiscrTree_Main(
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
pub unsafe fn initialize_Lean_Meta_DiscrTree_Main(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Lean_Meta_DiscrTree_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_DiscrTree_Main(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_DiscrTree_Main(builtin);
}