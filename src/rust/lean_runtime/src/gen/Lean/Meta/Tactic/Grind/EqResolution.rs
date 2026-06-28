// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EqResolution
// Imports: Lean.Meta.Basic Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Util.ForEachExpr
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hasExprMVar,
    l_Lean_Expr_hasMVar, l_Lean_Expr_hash, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_isMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEqRefl, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp,
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_mkLambdaFVars, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::MatchUtil::{
    initialize_Lean_Meta_MatchUtil, l_Lean_Meta_matchNot_x3f,
    runtime_initialize_Lean_Meta_MatchUtil,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::ForEachExpr::{
    initialize_Lean_Util_ForEachExpr, runtime_initialize_Lean_Util_ForEachExpr,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_checked_assign, lean_infer_type};
pub static l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__0_value) as *mut crate::leanh::LeanObject,907667957179513571 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_eqResolution___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [104, 0],
    };
static mut l_Lean_Meta_Grind_eqResolution___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eqResolution___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_eqResolution___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_eqResolution___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8738205681931236784 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_eqResolution___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_eqResolution___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1764_ = crate::leanh::lean_box(0);
    v___x_1765_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__1;
    v___x_1766_ = l_Lean_mkConst(v___x_1765_, v___x_1764_);
    return v___x_1766_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(
    mut v_prop_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v_a_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1817_: u8 = 0;
    let mut v_a_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_unused_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1773_ = crate::leanh::lean_box(0);
                v___x_1774_ = 0;
                v___x_1775_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_prop_1767_,
                    v___x_1773_,
                    v___x_1774_,
                    v_a_1768_,
                    v_a_1769_,
                    v_a_1770_,
                    v_a_1771_,
                );
                if crate::leanh::lean_obj_tag(v___x_1775_) == 0 {
                    v_a_1776_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                    crate::leanh::lean_inc(v_a_1776_);
                    crate::leanh::lean_dec_ref_known(v___x_1775_, 1);
                    v_snd_1777_ = crate::leanh::lean_ctor_get(v_a_1776_, 1);
                    crate::leanh::lean_inc(v_snd_1777_);
                    v_fst_1778_ = crate::leanh::lean_ctor_get(v_a_1776_, 0);
                    crate::leanh::lean_inc(v_fst_1778_);
                    crate::leanh::lean_dec(v_a_1776_);
                    v_snd_1779_ = crate::leanh::lean_ctor_get(v_snd_1777_, 1);
                    v_isSharedCheck_1826_ = (!crate::leanh::lean_is_exclusive(v_snd_1777_)) as u8;
                    if v_isSharedCheck_1826_ == 0 {
                        v_unused_1827_ = crate::leanh::lean_ctor_get(v_snd_1777_, 0);
                        crate::leanh::lean_dec(v_unused_1827_);
                        v___x_1781_ = v_snd_1777_;
                        v_isShared_1782_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1779_);
                        crate::leanh::lean_dec(v_snd_1777_);
                        v___x_1781_ = crate::leanh::lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1826_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1828_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1835_ = (!crate::leanh::lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1830_ = v___x_1775_;
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1828_);
                        crate::leanh::lean_dec(v___x_1775_);
                        v___x_1830_ = crate::leanh::lean_box(0);
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_snd_1779_);
                v___x_1783_ = l_Lean_Meta_matchNot_x3f(
                    v_snd_1779_,
                    v_a_1768_,
                    v_a_1769_,
                    v_a_1770_,
                    v_a_1771_,
                );
                if crate::leanh::lean_obj_tag(v___x_1783_) == 0 {
                    v_a_1784_ = crate::leanh::lean_ctor_get(v___x_1783_, 0);
                    v_isSharedCheck_1817_ = (!crate::leanh::lean_is_exclusive(v___x_1783_)) as u8;
                    if v_isSharedCheck_1817_ == 0 {
                        v___x_1786_ = v___x_1783_;
                        v_isShared_1787_ = v_isSharedCheck_1817_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1784_);
                        crate::leanh::lean_dec(v___x_1783_);
                        v___x_1786_ = crate::leanh::lean_box(0);
                        v_isShared_1787_ = v_isSharedCheck_1817_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1781_);
                    crate::leanh::lean_dec(v_snd_1779_);
                    crate::leanh::lean_dec(v_fst_1778_);
                    v_a_1818_ = crate::leanh::lean_ctor_get(v___x_1783_, 0);
                    v_isSharedCheck_1825_ = (!crate::leanh::lean_is_exclusive(v___x_1783_)) as u8;
                    if v_isSharedCheck_1825_ == 0 {
                        v___x_1820_ = v___x_1783_;
                        v_isShared_1821_ = v_isSharedCheck_1825_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1818_);
                        crate::leanh::lean_dec(v___x_1783_);
                        v___x_1820_ = crate::leanh::lean_box(0);
                        v_isShared_1821_ = v_isSharedCheck_1825_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1784_) == 1 {
                    crate::leanh::lean_del_object(v___x_1786_);
                    crate::leanh::lean_dec(v_snd_1779_);
                    v___x_1788_ = crate::leanh::lean_box(0);
                    v___x_1789_ = l_Lean_Meta_mkFreshExprMVar(
                        v_a_1784_,
                        v___x_1774_,
                        v___x_1788_,
                        v_a_1768_,
                        v_a_1769_,
                        v_a_1770_,
                        v_a_1771_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1789_) == 0 {
                        v_a_1790_ = crate::leanh::lean_ctor_get(v___x_1789_, 0);
                        v_isSharedCheck_1802_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1789_)) as u8;
                        if v_isSharedCheck_1802_ == 0 {
                            v___x_1792_ = v___x_1789_;
                            v_isShared_1793_ = v_isSharedCheck_1802_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1790_);
                            crate::leanh::lean_dec(v___x_1789_);
                            v___x_1792_ = crate::leanh::lean_box(0);
                            v_isShared_1793_ = v_isSharedCheck_1802_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1781_);
                        crate::leanh::lean_dec(v_fst_1778_);
                        v_a_1803_ = crate::leanh::lean_ctor_get(v___x_1789_, 0);
                        v_isSharedCheck_1810_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1789_)) as u8;
                        if v_isSharedCheck_1810_ == 0 {
                            v___x_1805_ = v___x_1789_;
                            v_isShared_1806_ = v_isSharedCheck_1810_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1803_);
                            crate::leanh::lean_dec(v___x_1789_);
                            v___x_1805_ = crate::leanh::lean_box(0);
                            v_isShared_1806_ = v_isSharedCheck_1810_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1784_);
                    if v_isShared_1782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1781_, 0, v_fst_1778_);
                        v___x_1812_ = v___x_1781_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1816_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_fst_1778_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_snd_1779_);
                        v___x_1812_ = v_reuseFailAlloc_1816_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1794_ = lean_array_push(v_fst_1778_, v_a_1790_);
                v___x_1795_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___closed__2);
                if v_isShared_1782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1781_, 1, v___x_1795_);
                    crate::leanh::lean_ctor_set(v___x_1781_, 0, v___x_1794_);
                    v___x_1797_ = v___x_1781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1801_, 1, v___x_1795_);
                    v___x_1797_ = v_reuseFailAlloc_1801_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1793_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1792_, 0, v___x_1797_);
                    v___x_1799_ = v___x_1792_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1800_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
                    v___x_1799_ = v_reuseFailAlloc_1800_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1799_;
            }
            6 => {
                if v_isShared_1806_ == 0 {
                    v___x_1808_ = v___x_1805_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
                    v___x_1808_ = v_reuseFailAlloc_1809_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1808_;
            }
            8 => {
                if v_isShared_1787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1786_, 0, v___x_1812_);
                    v___x_1814_ = v___x_1786_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
                    v___x_1814_ = v_reuseFailAlloc_1815_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1814_;
            }
            10 => {
                if v_isShared_1821_ == 0 {
                    v___x_1823_ = v___x_1820_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
                    v___x_1823_ = v_reuseFailAlloc_1824_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1823_;
            }
            12 => {
                if v_isShared_1831_ == 0 {
                    v___x_1833_ = v___x_1830_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
                    v___x_1833_ = v_reuseFailAlloc_1834_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot___boxed(
    mut v_prop_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1842_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(v_prop_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
    crate::leanh::lean_dec(v_a_1840_);
    crate::leanh::lean_dec_ref(v_a_1839_);
    crate::leanh::lean_dec(v_a_1838_);
    crate::leanh::lean_dec_ref(v_a_1837_);
    return v_res_1842_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(
    mut v_e_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_unused_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1847_ = l_Lean_Expr_hasMVar(v_e_1843_);
                if v___x_1847_ == 0 {
                    v___x_1848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1848_, 0, v_e_1843_);
                    v___x_1849_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1848_);
                    crate::leanh::lean_ctor_set(v___x_1849_, 1, v___y_1844_);
                    v___x_1850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1850_, 0, v___x_1849_);
                    return v___x_1850_;
                } else {
                    v___x_1851_ = lean_st_ref_get(v___y_1845_);
                    v_mctx_1852_ = crate::leanh::lean_ctor_get(v___x_1851_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1852_);
                    crate::leanh::lean_dec(v___x_1851_);
                    v___x_1853_ = l_Lean_instantiateMVarsCore(v_mctx_1852_, v_e_1843_);
                    v_fst_1854_ = crate::leanh::lean_ctor_get(v___x_1853_, 0);
                    v_snd_1855_ = crate::leanh::lean_ctor_get(v___x_1853_, 1);
                    v_isSharedCheck_1878_ = (!crate::leanh::lean_is_exclusive(v___x_1853_)) as u8;
                    if v_isSharedCheck_1878_ == 0 {
                        v___x_1857_ = v___x_1853_;
                        v_isShared_1858_ = v_isSharedCheck_1878_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1855_);
                        crate::leanh::lean_inc(v_fst_1854_);
                        crate::leanh::lean_dec(v___x_1853_);
                        v___x_1857_ = crate::leanh::lean_box(0);
                        v_isShared_1858_ = v_isSharedCheck_1878_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1859_ = lean_st_ref_take(v___y_1845_);
                v_cache_1860_ = crate::leanh::lean_ctor_get(v___x_1859_, 1);
                v_zetaDeltaFVarIds_1861_ = crate::leanh::lean_ctor_get(v___x_1859_, 2);
                v_postponed_1862_ = crate::leanh::lean_ctor_get(v___x_1859_, 3);
                v_diag_1863_ = crate::leanh::lean_ctor_get(v___x_1859_, 4);
                v_isSharedCheck_1876_ = (!crate::leanh::lean_is_exclusive(v___x_1859_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v_unused_1877_ = crate::leanh::lean_ctor_get(v___x_1859_, 0);
                    crate::leanh::lean_dec(v_unused_1877_);
                    v___x_1865_ = v___x_1859_;
                    v_isShared_1866_ = v_isSharedCheck_1876_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1863_);
                    crate::leanh::lean_inc(v_postponed_1862_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1861_);
                    crate::leanh::lean_inc(v_cache_1860_);
                    crate::leanh::lean_dec(v___x_1859_);
                    v___x_1865_ = crate::leanh::lean_box(0);
                    v_isShared_1866_ = v_isSharedCheck_1876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1866_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1865_, 0, v_snd_1855_);
                    v___x_1868_ = v___x_1865_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_snd_1855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 1, v_cache_1860_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1875_,
                        2,
                        v_zetaDeltaFVarIds_1861_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 3, v_postponed_1862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 4, v_diag_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1869_ = lean_st_ref_set(v___y_1845_, v___x_1868_);
                v___x_1870_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1870_, 0, v_fst_1854_);
                if v_isShared_1858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1857_, 1, v___y_1844_);
                    crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1870_);
                    v___x_1872_ = v___x_1857_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___y_1844_);
                    v___x_1872_ = v_reuseFailAlloc_1874_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                return v___x_1873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg___boxed(
    mut v_e_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(v_e_1879_, v___y_1880_, v___y_1881_);
    crate::leanh::lean_dec(v___y_1881_);
    return v_res_1883_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5(
    mut v_a_1884_: *mut crate::leanh::LeanObject,
    mut v_as_1885_: *mut crate::leanh::LeanObject,
    mut v_i_1886_: usize,
    mut v_stop_1887_: usize,
) -> u8 {
    let mut v___x_1888_: u8 = 0;
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v___x_1891_: usize = 0;
    let mut v___x_1892_: usize = 0;
    let mut v___x_1894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1888_ = lean_usize_dec_eq(v_i_1886_, v_stop_1887_);
                if v___x_1888_ == 0 {
                    v___x_1889_ = lean_array_uget_borrowed(v_as_1885_, v_i_1886_);
                    v___x_1890_ = lean_expr_eqv(v_a_1884_, v___x_1889_);
                    if v___x_1890_ == 0 {
                        v___x_1891_ = 1usize;
                        v___x_1892_ = lean_usize_add(v_i_1886_, v___x_1891_);
                        v_i_1886_ = v___x_1892_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1890_;
                    }
                } else {
                    v___x_1894_ = 0;
                    return v___x_1894_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5___boxed(
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_as_1896_: *mut crate::leanh::LeanObject,
    mut v_i_1897_: *mut crate::leanh::LeanObject,
    mut v_stop_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1899_: usize = 0;
    let mut v_stop_boxed_1900_: usize = 0;
    let mut v_res_1901_: u8 = 0;
    let mut v_r_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1899_ = crate::leanh::lean_unbox_usize(v_i_1897_);
    crate::leanh::lean_dec(v_i_1897_);
    v_stop_boxed_1900_ = crate::leanh::lean_unbox_usize(v_stop_1898_);
    crate::leanh::lean_dec(v_stop_1898_);
    v_res_1901_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5(v_a_1895_, v_as_1896_, v_i_boxed_1899_, v_stop_boxed_1900_);
    crate::leanh::lean_dec_ref(v_as_1896_);
    crate::leanh::lean_dec_ref(v_a_1895_);
    v_r_1902_ = crate::leanh::lean_box((v_res_1901_) as usize);
    return v_r_1902_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3(
    mut v_as_1903_: *mut crate::leanh::LeanObject,
    mut v_a_1904_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    v___x_1905_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1906_ = lean_array_get_size(v_as_1903_);
    v___x_1907_ = lean_nat_dec_lt(v___x_1905_, v___x_1906_);
    if v___x_1907_ == 0 {
        return v___x_1907_;
    } else {
        if v___x_1907_ == 0 {
            return v___x_1907_;
        } else {
            let mut v___x_1908_: usize = 0;
            let mut v___x_1909_: usize = 0;
            let mut v___x_1910_: u8 = 0;
            v___x_1908_ = 0usize;
            v___x_1909_ = lean_usize_of_nat(v___x_1906_);
            v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3_spec__5(v_a_1904_, v_as_1903_, v___x_1908_, v___x_1909_);
            return v___x_1910_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3___boxed(
    mut v_as_1911_: *mut crate::leanh::LeanObject,
    mut v_a_1912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1913_: u8 = 0;
    let mut v_r_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1913_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3(v_as_1911_, v_a_1912_);
    crate::leanh::lean_dec_ref(v_a_1912_);
    crate::leanh::lean_dec_ref(v_as_1911_);
    v_r_1914_ = crate::leanh::lean_box((v_res_1913_) as usize);
    return v_r_1914_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(
    mut v_a_1915_: *mut crate::leanh::LeanObject,
    mut v_x_1916_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1917_: u8 = 0;
    let mut v_key_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1916_) == 0 {
                    v___x_1917_ = 0;
                    return v___x_1917_;
                } else {
                    v_key_1918_ = crate::leanh::lean_ctor_get(v_x_1916_, 0);
                    v_tail_1919_ = crate::leanh::lean_ctor_get(v_x_1916_, 2);
                    v___x_1920_ = lean_expr_eqv(v_key_1918_, v_a_1915_);
                    if v___x_1920_ == 0 {
                        v_x_1916_ = v_tail_1919_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1920_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg___boxed(
    mut v_a_1922_: *mut crate::leanh::LeanObject,
    mut v_x_1923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1924_: u8 = 0;
    let mut v_r_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(v_a_1922_, v_x_1923_);
    crate::leanh::lean_dec(v_x_1923_);
    crate::leanh::lean_dec_ref(v_a_1922_);
    v_r_1925_ = crate::leanh::lean_box((v_res_1924_) as usize);
    return v_r_1925_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8___redArg(
    mut v_x_1926_: *mut crate::leanh::LeanObject,
    mut v_x_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1933_: u8 = 0;
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u64 = 0;
    let mut v___x_1936_: u64 = 0;
    let mut v___x_1937_: u64 = 0;
    let mut v_fold_1938_: u64 = 0;
    let mut v___x_1939_: u64 = 0;
    let mut v___x_1940_: u64 = 0;
    let mut v___x_1941_: u64 = 0;
    let mut v___x_1942_: usize = 0;
    let mut v___x_1943_: usize = 0;
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut v___x_1946_: usize = 0;
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1927_) == 0 {
                    return v_x_1926_;
                } else {
                    v_key_1928_ = crate::leanh::lean_ctor_get(v_x_1927_, 0);
                    v_value_1929_ = crate::leanh::lean_ctor_get(v_x_1927_, 1);
                    v_tail_1930_ = crate::leanh::lean_ctor_get(v_x_1927_, 2);
                    v_isSharedCheck_1953_ = (!crate::leanh::lean_is_exclusive(v_x_1927_)) as u8;
                    if v_isSharedCheck_1953_ == 0 {
                        v___x_1932_ = v_x_1927_;
                        v_isShared_1933_ = v_isSharedCheck_1953_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1930_);
                        crate::leanh::lean_inc(v_value_1929_);
                        crate::leanh::lean_inc(v_key_1928_);
                        crate::leanh::lean_dec(v_x_1927_);
                        v___x_1932_ = crate::leanh::lean_box(0);
                        v_isShared_1933_ = v_isSharedCheck_1953_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1934_ = lean_array_get_size(v_x_1926_);
                v___x_1935_ = l_Lean_Expr_hash(v_key_1928_);
                v___x_1936_ = 32u64;
                v___x_1937_ = lean_uint64_shift_right(v___x_1935_, v___x_1936_);
                v_fold_1938_ = lean_uint64_xor(v___x_1935_, v___x_1937_);
                v___x_1939_ = 16u64;
                v___x_1940_ = lean_uint64_shift_right(v_fold_1938_, v___x_1939_);
                v___x_1941_ = lean_uint64_xor(v_fold_1938_, v___x_1940_);
                v___x_1942_ = lean_uint64_to_usize(v___x_1941_);
                v___x_1943_ = lean_usize_of_nat(v___x_1934_);
                v___x_1944_ = 1usize;
                v___x_1945_ = lean_usize_sub(v___x_1943_, v___x_1944_);
                v___x_1946_ = lean_usize_land(v___x_1942_, v___x_1945_);
                v___x_1947_ = lean_array_uget_borrowed(v_x_1926_, v___x_1946_);
                crate::leanh::lean_inc(v___x_1947_);
                if v_isShared_1933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1932_, 2, v___x_1947_);
                    v___x_1949_ = v___x_1932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1952_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_key_1928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_value_1929_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1952_, 2, v___x_1947_);
                    v___x_1949_ = v_reuseFailAlloc_1952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1950_ = lean_array_uset(v_x_1926_, v___x_1946_, v___x_1949_);
                v_x_1926_ = v___x_1950_;
                v_x_1927_ = v_tail_1930_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5___redArg(
    mut v_i_1954_: *mut crate::leanh::LeanObject,
    mut v_source_1955_: *mut crate::leanh::LeanObject,
    mut v_target_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: u8 = 0;
    let mut v_es_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1957_ = lean_array_get_size(v_source_1955_);
                v___x_1958_ = lean_nat_dec_lt(v_i_1954_, v___x_1957_);
                if v___x_1958_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_1955_);
                    crate::leanh::lean_dec(v_i_1954_);
                    return v_target_1956_;
                } else {
                    v_es_1959_ = lean_array_fget(v_source_1955_, v_i_1954_);
                    v___x_1960_ = crate::leanh::lean_box(0);
                    v_source_1961_ = lean_array_fset(v_source_1955_, v_i_1954_, v___x_1960_);
                    v_target_1962_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8___redArg(v_target_1956_, v_es_1959_);
                    v___x_1963_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1964_ = lean_nat_add(v_i_1954_, v___x_1963_);
                    crate::leanh::lean_dec(v_i_1954_);
                    v_i_1954_ = v___x_1964_;
                    v_source_1955_ = v_source_1961_;
                    v_target_1956_ = v_target_1962_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(
    mut v_data_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1967_ = lean_array_get_size(v_data_1966_);
    v___x_1968_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_1969_ = lean_nat_mul(v___x_1967_, v___x_1968_);
    v___x_1970_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1971_ = crate::leanh::lean_box(0);
    v___x_1972_ = lean_mk_array(v_nbuckets_1969_, v___x_1971_);
    v___x_1973_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5___redArg(v___x_1970_, v_data_1966_, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v_b_1975_: *mut crate::leanh::LeanObject,
    mut v_x_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1982_: u8 = 0;
    let mut v___x_1983_: u8 = 0;
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1976_) == 0 {
                    crate::leanh::lean_dec(v_b_1975_);
                    crate::leanh::lean_dec_ref(v_a_1974_);
                    return v_x_1976_;
                } else {
                    v_key_1977_ = crate::leanh::lean_ctor_get(v_x_1976_, 0);
                    v_value_1978_ = crate::leanh::lean_ctor_get(v_x_1976_, 1);
                    v_tail_1979_ = crate::leanh::lean_ctor_get(v_x_1976_, 2);
                    v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v_x_1976_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1981_ = v_x_1976_;
                        v_isShared_1982_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1979_);
                        crate::leanh::lean_inc(v_value_1978_);
                        crate::leanh::lean_inc(v_key_1977_);
                        crate::leanh::lean_dec(v_x_1976_);
                        v___x_1981_ = crate::leanh::lean_box(0);
                        v_isShared_1982_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1983_ = lean_expr_eqv(v_key_1977_, v_a_1974_);
                if v___x_1983_ == 0 {
                    v___x_1984_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(v_a_1974_, v_b_1975_, v_tail_1979_);
                    if v_isShared_1982_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1981_, 2, v___x_1984_);
                        v___x_1986_ = v___x_1981_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_key_1977_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_value_1978_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 2, v___x_1984_);
                        v___x_1986_ = v_reuseFailAlloc_1987_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_1978_);
                    crate::leanh::lean_dec(v_key_1977_);
                    if v_isShared_1982_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1981_, 1, v_b_1975_);
                        crate::leanh::lean_ctor_set(v___x_1981_, 0, v_a_1974_);
                        v___x_1989_ = v___x_1981_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1974_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_b_1975_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_tail_1979_);
                        v___x_1989_ = v_reuseFailAlloc_1990_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1986_;
            }
            3 => {
                return v___x_1989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9___redArg(
    mut v_m_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_b_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u64 = 0;
    let mut v___x_2002_: u64 = 0;
    let mut v___x_2003_: u64 = 0;
    let mut v_fold_2004_: u64 = 0;
    let mut v___x_2005_: u64 = 0;
    let mut v___x_2006_: u64 = 0;
    let mut v___x_2007_: u64 = 0;
    let mut v___x_2008_: usize = 0;
    let mut v___x_2009_: usize = 0;
    let mut v___x_2010_: usize = 0;
    let mut v___x_2011_: usize = 0;
    let mut v___x_2012_: usize = 0;
    let mut v_bkt_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v_val_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1995_ = crate::leanh::lean_ctor_get(v_m_1992_, 0);
                v_buckets_1996_ = crate::leanh::lean_ctor_get(v_m_1992_, 1);
                v_isSharedCheck_2039_ = (!crate::leanh::lean_is_exclusive(v_m_1992_)) as u8;
                if v_isSharedCheck_2039_ == 0 {
                    v___x_1998_ = v_m_1992_;
                    v_isShared_1999_ = v_isSharedCheck_2039_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_1996_);
                    crate::leanh::lean_inc(v_size_1995_);
                    crate::leanh::lean_dec(v_m_1992_);
                    v___x_1998_ = crate::leanh::lean_box(0);
                    v_isShared_1999_ = v_isSharedCheck_2039_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2000_ = lean_array_get_size(v_buckets_1996_);
                v___x_2001_ = l_Lean_Expr_hash(v_a_1993_);
                v___x_2002_ = 32u64;
                v___x_2003_ = lean_uint64_shift_right(v___x_2001_, v___x_2002_);
                v_fold_2004_ = lean_uint64_xor(v___x_2001_, v___x_2003_);
                v___x_2005_ = 16u64;
                v___x_2006_ = lean_uint64_shift_right(v_fold_2004_, v___x_2005_);
                v___x_2007_ = lean_uint64_xor(v_fold_2004_, v___x_2006_);
                v___x_2008_ = lean_uint64_to_usize(v___x_2007_);
                v___x_2009_ = lean_usize_of_nat(v___x_2000_);
                v___x_2010_ = 1usize;
                v___x_2011_ = lean_usize_sub(v___x_2009_, v___x_2010_);
                v___x_2012_ = lean_usize_land(v___x_2008_, v___x_2011_);
                v_bkt_2013_ = lean_array_uget_borrowed(v_buckets_1996_, v___x_2012_);
                v___x_2014_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(v_a_1993_, v_bkt_2013_);
                if v___x_2014_ == 0 {
                    v___x_2015_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_2016_ = lean_nat_add(v_size_1995_, v___x_2015_);
                    crate::leanh::lean_dec(v_size_1995_);
                    crate::leanh::lean_inc(v_bkt_2013_);
                    v___x_2017_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2017_, 0, v_a_1993_);
                    crate::leanh::lean_ctor_set(v___x_2017_, 1, v_b_1994_);
                    crate::leanh::lean_ctor_set(v___x_2017_, 2, v_bkt_2013_);
                    v_buckets_x27_2018_ =
                        lean_array_uset(v_buckets_1996_, v___x_2012_, v___x_2017_);
                    v___x_2019_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2020_ = lean_nat_mul(v_size_x27_2016_, v___x_2019_);
                    v___x_2021_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2022_ = lean_nat_div(v___x_2020_, v___x_2021_);
                    crate::leanh::lean_dec(v___x_2020_);
                    v___x_2023_ = lean_array_get_size(v_buckets_x27_2018_);
                    v___x_2024_ = lean_nat_dec_le(v___x_2022_, v___x_2023_);
                    crate::leanh::lean_dec(v___x_2022_);
                    if v___x_2024_ == 0 {
                        v_val_2025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(v_buckets_x27_2018_);
                        if v_isShared_1999_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1998_, 1, v_val_2025_);
                            crate::leanh::lean_ctor_set(v___x_1998_, 0, v_size_x27_2016_);
                            v___x_2027_ = v___x_1998_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2028_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2028_,
                                0,
                                v_size_x27_2016_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_val_2025_);
                            v___x_2027_ = v_reuseFailAlloc_2028_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_1999_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1998_, 1, v_buckets_x27_2018_);
                            crate::leanh::lean_ctor_set(v___x_1998_, 0, v_size_x27_2016_);
                            v___x_2030_ = v___x_1998_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2031_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2031_,
                                0,
                                v_size_x27_2016_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_2031_,
                                1,
                                v_buckets_x27_2018_,
                            );
                            v___x_2030_ = v_reuseFailAlloc_2031_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_2013_);
                    v___x_2032_ = crate::leanh::lean_box(0);
                    v_buckets_x27_2033_ =
                        lean_array_uset(v_buckets_1996_, v___x_2012_, v___x_2032_);
                    v___x_2034_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(v_a_1993_, v_b_1994_, v_bkt_2013_);
                    v___x_2035_ = lean_array_uset(v_buckets_x27_2033_, v___x_2012_, v___x_2034_);
                    if v_isShared_1999_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1998_, 1, v___x_2035_);
                        v___x_2037_ = v___x_1998_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_size_1995_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2035_);
                        v___x_2037_ = v_reuseFailAlloc_2038_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2027_;
            }
            3 => {
                return v___x_2030_;
            }
            4 => {
                return v___x_2037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_x_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2041_) == 0 {
                    v___x_2042_ = crate::leanh::lean_box(0);
                    return v___x_2042_;
                } else {
                    v_key_2043_ = crate::leanh::lean_ctor_get(v_x_2041_, 0);
                    v_value_2044_ = crate::leanh::lean_ctor_get(v_x_2041_, 1);
                    v_tail_2045_ = crate::leanh::lean_ctor_get(v_x_2041_, 2);
                    v___x_2046_ = lean_expr_eqv(v_key_2043_, v_a_2040_);
                    if v___x_2046_ == 0 {
                        v_x_2041_ = v_tail_2045_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2044_);
                        v___x_2048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2048_, 0, v_value_2044_);
                        return v___x_2048_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg___boxed(
    mut v_a_2049_: *mut crate::leanh::LeanObject,
    mut v_x_2050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(v_a_2049_, v_x_2050_);
    crate::leanh::lean_dec(v_x_2050_);
    crate::leanh::lean_dec_ref(v_a_2049_);
    return v_res_2051_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(
    mut v_m_2052_: *mut crate::leanh::LeanObject,
    mut v_a_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u64 = 0;
    let mut v___x_2057_: u64 = 0;
    let mut v___x_2058_: u64 = 0;
    let mut v_fold_2059_: u64 = 0;
    let mut v___x_2060_: u64 = 0;
    let mut v___x_2061_: u64 = 0;
    let mut v___x_2062_: u64 = 0;
    let mut v___x_2063_: usize = 0;
    let mut v___x_2064_: usize = 0;
    let mut v___x_2065_: usize = 0;
    let mut v___x_2066_: usize = 0;
    let mut v___x_2067_: usize = 0;
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2054_ = crate::leanh::lean_ctor_get(v_m_2052_, 1);
    v___x_2055_ = lean_array_get_size(v_buckets_2054_);
    v___x_2056_ = l_Lean_Expr_hash(v_a_2053_);
    v___x_2057_ = 32u64;
    v___x_2058_ = lean_uint64_shift_right(v___x_2056_, v___x_2057_);
    v_fold_2059_ = lean_uint64_xor(v___x_2056_, v___x_2058_);
    v___x_2060_ = 16u64;
    v___x_2061_ = lean_uint64_shift_right(v_fold_2059_, v___x_2060_);
    v___x_2062_ = lean_uint64_xor(v_fold_2059_, v___x_2061_);
    v___x_2063_ = lean_uint64_to_usize(v___x_2062_);
    v___x_2064_ = lean_usize_of_nat(v___x_2055_);
    v___x_2065_ = 1usize;
    v___x_2066_ = lean_usize_sub(v___x_2064_, v___x_2065_);
    v___x_2067_ = lean_usize_land(v___x_2063_, v___x_2066_);
    v___x_2068_ = lean_array_uget_borrowed(v_buckets_2054_, v___x_2067_);
    v___x_2069_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(v_a_2053_, v___x_2068_);
    return v___x_2069_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg___boxed(
    mut v_m_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(v_m_2070_, v_a_2071_);
    crate::leanh::lean_dec_ref(v_a_2071_);
    crate::leanh::lean_dec_ref(v_m_2070_);
    return v_res_2072_;
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(
    mut v_g_2075_: *mut crate::leanh::LeanObject,
    mut v_e_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v_fst_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v_d_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2166_: u8 = 0;
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2171_: u8 = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2100_ = lean_st_ref_get(v_a_2077_);
                v___x_2101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(v___x_2100_, v_e_2076_);
                crate::leanh::lean_dec(v___x_2100_);
                if crate::leanh::lean_obj_tag(v___x_2101_) == 0 {
                    crate::leanh::lean_inc_ref(v_g_2075_);
                    crate::leanh::lean_inc(v___y_2082_);
                    crate::leanh::lean_inc_ref(v___y_2081_);
                    crate::leanh::lean_inc(v___y_2080_);
                    crate::leanh::lean_inc_ref(v___y_2079_);
                    crate::leanh::lean_inc_ref(v_e_2076_);
                    v___x_2102_ = crate::leanh::lean_apply_7(
                        v_g_2075_,
                        v_e_2076_,
                        v___y_2078_,
                        v___y_2079_,
                        v___y_2080_,
                        v___y_2081_,
                        v___y_2082_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_2102_) == 0 {
                        v_a_2103_ = crate::leanh::lean_ctor_get(v___x_2102_, 0);
                        v_isSharedCheck_2167_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2102_)) as u8;
                        if v_isSharedCheck_2167_ == 0 {
                            v___x_2105_ = v___x_2102_;
                            v_isShared_2106_ = v_isSharedCheck_2167_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2103_);
                            crate::leanh::lean_dec(v___x_2102_);
                            v___x_2105_ = crate::leanh::lean_box(0);
                            v_isShared_2106_ = v_isSharedCheck_2167_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2076_);
                        crate::leanh::lean_dec_ref(v_g_2075_);
                        v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2102_, 0);
                        v_isSharedCheck_2175_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2102_)) as u8;
                        if v_isSharedCheck_2175_ == 0 {
                            v___x_2170_ = v___x_2102_;
                            v_isShared_2171_ = v_isSharedCheck_2175_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2168_);
                            crate::leanh::lean_dec(v___x_2102_);
                            v___x_2170_ = crate::leanh::lean_box(0);
                            v_isShared_2171_ = v_isSharedCheck_2175_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2076_);
                    crate::leanh::lean_dec_ref(v_g_2075_);
                    v___x_2176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2176_, 0, v___x_2101_);
                    crate::leanh::lean_ctor_set(v___x_2176_, 1, v___y_2078_);
                    v___x_2177_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
                    return v___x_2177_;
                }
            }
            1 => {
                v___x_2087_ = lean_st_ref_take(v_a_2077_);
                v___x_2088_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9___redArg(v___x_2087_, v_e_2076_, v_val_2086_);
                v___x_2089_ = lean_st_ref_set(v_a_2077_, v___x_2088_);
                v___x_2090_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2090_, 0, v_a_2085_);
                return v___x_2090_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_fst_2094_) == 0 {
                    crate::leanh::lean_dec_ref(v_a_2093_);
                    crate::leanh::lean_dec_ref(v_e_2076_);
                    return v___y_2092_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_2092_);
                    v_val_2095_ = crate::leanh::lean_ctor_get(v_fst_2094_, 0);
                    crate::leanh::lean_inc(v_val_2095_);
                    crate::leanh::lean_dec_ref_known(v_fst_2094_, 1);
                    v_a_2085_ = v_a_2093_;
                    v_val_2086_ = v_val_2095_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_2097_) == 0 {
                    v_a_2098_ = crate::leanh::lean_ctor_get(v___y_2097_, 0);
                    crate::leanh::lean_inc(v_a_2098_);
                    v_fst_2099_ = crate::leanh::lean_ctor_get(v_a_2098_, 0);
                    crate::leanh::lean_inc(v_fst_2099_);
                    v___y_2092_ = v___y_2097_;
                    v_a_2093_ = v_a_2098_;
                    v_fst_2094_ = v_fst_2099_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_2076_);
                    return v___y_2097_;
                }
            }
            4 => {
                v_fst_2107_ = crate::leanh::lean_ctor_get(v_a_2103_, 0);
                v_snd_2108_ = crate::leanh::lean_ctor_get(v_a_2103_, 1);
                v_isSharedCheck_2166_ = (!crate::leanh::lean_is_exclusive(v_a_2103_)) as u8;
                if v_isSharedCheck_2166_ == 0 {
                    v___x_2110_ = v_a_2103_;
                    v_isShared_2111_ = v_isSharedCheck_2166_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2108_);
                    crate::leanh::lean_inc(v_fst_2107_);
                    crate::leanh::lean_dec(v_a_2103_);
                    v___x_2110_ = crate::leanh::lean_box(0);
                    v_isShared_2111_ = v_isSharedCheck_2166_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_fst_2107_) == 0 {
                    crate::leanh::lean_dec_ref(v_g_2075_);
                    if v_isShared_2111_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2101_);
                        v___x_2122_ = v___x_2110_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2101_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2126_, 1, v_snd_2108_);
                        v___x_2122_ = v_reuseFailAlloc_2126_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2105_);
                    v_val_2127_ = crate::leanh::lean_ctor_get(v_fst_2107_, 0);
                    crate::leanh::lean_inc(v_val_2127_);
                    crate::leanh::lean_dec_ref_known(v_fst_2107_, 1);
                    v___x_2128_ = (crate::leanh::lean_unbox(v_val_2127_) as u8);
                    crate::leanh::lean_dec(v_val_2127_);
                    if v___x_2128_ == 0 {
                        crate::leanh::lean_dec_ref(v_g_2075_);
                        v___x_2129_ = crate::leanh::lean_box(0);
                        v___x_2130_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
                        if v_isShared_2111_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2130_);
                            v___x_2132_ = v___x_2110_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2133_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_snd_2108_);
                            v___x_2132_ = v_reuseFailAlloc_2133_;
                            state = 9;
                            continue;
                        }
                    } else {
                        match crate::leanh::lean_obj_tag(v_e_2076_) {
                            7 => {
                                crate::leanh::lean_del_object(v___x_2110_);
                                v_binderType_2134_ = crate::leanh::lean_ctor_get(v_e_2076_, 1);
                                v_body_2135_ = crate::leanh::lean_ctor_get(v_e_2076_, 2);
                                crate::leanh::lean_inc_ref(v_body_2135_);
                                crate::leanh::lean_inc_ref(v_binderType_2134_);
                                v_d_2113_ = v_binderType_2134_;
                                v_b_2114_ = v_body_2135_;
                                v___y_2115_ = v_a_2077_;
                                state = 6;
                                continue;
                            }
                            6 => {
                                crate::leanh::lean_del_object(v___x_2110_);
                                v_binderType_2136_ = crate::leanh::lean_ctor_get(v_e_2076_, 1);
                                v_body_2137_ = crate::leanh::lean_ctor_get(v_e_2076_, 2);
                                crate::leanh::lean_inc_ref(v_body_2137_);
                                crate::leanh::lean_inc_ref(v_binderType_2136_);
                                v_d_2113_ = v_binderType_2136_;
                                v_b_2114_ = v_body_2137_;
                                v___y_2115_ = v_a_2077_;
                                state = 6;
                                continue;
                            }
                            8 => {
                                crate::leanh::lean_del_object(v___x_2110_);
                                v_type_2138_ = crate::leanh::lean_ctor_get(v_e_2076_, 1);
                                v_value_2139_ = crate::leanh::lean_ctor_get(v_e_2076_, 2);
                                v_body_2140_ = crate::leanh::lean_ctor_get(v_e_2076_, 3);
                                crate::leanh::lean_inc_ref(v_type_2138_);
                                crate::leanh::lean_inc_ref(v_g_2075_);
                                v___x_2141_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_type_2138_, v_a_2077_, v_snd_2108_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                                if crate::leanh::lean_obj_tag(v___x_2141_) == 0 {
                                    v_a_2142_ = crate::leanh::lean_ctor_get(v___x_2141_, 0);
                                    crate::leanh::lean_inc(v_a_2142_);
                                    v_fst_2143_ = crate::leanh::lean_ctor_get(v_a_2142_, 0);
                                    if crate::leanh::lean_obj_tag(v_fst_2143_) == 0 {
                                        crate::leanh::lean_dec(v_a_2142_);
                                        crate::leanh::lean_dec_ref(v_g_2075_);
                                        v___y_2097_ = v___x_2141_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_2141_, 1);
                                        v_snd_2144_ = crate::leanh::lean_ctor_get(v_a_2142_, 1);
                                        crate::leanh::lean_inc(v_snd_2144_);
                                        crate::leanh::lean_dec(v_a_2142_);
                                        crate::leanh::lean_inc_ref(v_value_2139_);
                                        crate::leanh::lean_inc_ref(v_g_2075_);
                                        v___x_2145_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_value_2139_, v_a_2077_, v_snd_2144_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                                        if crate::leanh::lean_obj_tag(v___x_2145_) == 0 {
                                            v_a_2146_ = crate::leanh::lean_ctor_get(v___x_2145_, 0);
                                            crate::leanh::lean_inc(v_a_2146_);
                                            v_fst_2147_ = crate::leanh::lean_ctor_get(v_a_2146_, 0);
                                            if crate::leanh::lean_obj_tag(v_fst_2147_) == 0 {
                                                crate::leanh::lean_dec(v_a_2146_);
                                                crate::leanh::lean_dec_ref(v_g_2075_);
                                                v___y_2097_ = v___x_2145_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v___x_2145_, 1);
                                                v_snd_2148_ =
                                                    crate::leanh::lean_ctor_get(v_a_2146_, 1);
                                                crate::leanh::lean_inc(v_snd_2148_);
                                                crate::leanh::lean_dec(v_a_2146_);
                                                crate::leanh::lean_inc_ref(v_body_2140_);
                                                v___x_2149_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_body_2140_, v_a_2077_, v_snd_2148_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                                                v___y_2097_ = v___x_2149_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_g_2075_);
                                            v___y_2097_ = v___x_2145_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_g_2075_);
                                    v___y_2097_ = v___x_2141_;
                                    state = 3;
                                    continue;
                                }
                            }
                            5 => {
                                crate::leanh::lean_del_object(v___x_2110_);
                                v_fn_2150_ = crate::leanh::lean_ctor_get(v_e_2076_, 0);
                                v_arg_2151_ = crate::leanh::lean_ctor_get(v_e_2076_, 1);
                                crate::leanh::lean_inc_ref(v_fn_2150_);
                                crate::leanh::lean_inc_ref(v_g_2075_);
                                v___x_2152_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_fn_2150_, v_a_2077_, v_snd_2108_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                                if crate::leanh::lean_obj_tag(v___x_2152_) == 0 {
                                    v_a_2153_ = crate::leanh::lean_ctor_get(v___x_2152_, 0);
                                    crate::leanh::lean_inc(v_a_2153_);
                                    v_fst_2154_ = crate::leanh::lean_ctor_get(v_a_2153_, 0);
                                    if crate::leanh::lean_obj_tag(v_fst_2154_) == 0 {
                                        crate::leanh::lean_dec(v_a_2153_);
                                        crate::leanh::lean_dec_ref(v_g_2075_);
                                        v___y_2097_ = v___x_2152_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_2152_, 1);
                                        v_snd_2155_ = crate::leanh::lean_ctor_get(v_a_2153_, 1);
                                        crate::leanh::lean_inc(v_snd_2155_);
                                        crate::leanh::lean_dec(v_a_2153_);
                                        crate::leanh::lean_inc_ref(v_arg_2151_);
                                        v___x_2156_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_arg_2151_, v_a_2077_, v_snd_2155_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                                        v___y_2097_ = v___x_2156_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_g_2075_);
                                    v___y_2097_ = v___x_2152_;
                                    state = 3;
                                    continue;
                                }
                            }
                            10 => {
                                crate::leanh::lean_del_object(v___x_2110_);
                                v_expr_2157_ = crate::leanh::lean_ctor_get(v_e_2076_, 1);
                                crate::leanh::lean_inc_ref(v_expr_2157_);
                                v___x_2158_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_expr_2157_, v_a_2077_, v_snd_2108_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                                v___y_2097_ = v___x_2158_;
                                state = 3;
                                continue;
                            }
                            11 => {
                                crate::leanh::lean_del_object(v___x_2110_);
                                v_struct_2159_ = crate::leanh::lean_ctor_get(v_e_2076_, 2);
                                crate::leanh::lean_inc_ref(v_struct_2159_);
                                v___x_2160_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_struct_2159_, v_a_2077_, v_snd_2108_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                                v___y_2097_ = v___x_2160_;
                                state = 3;
                                continue;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref(v_g_2075_);
                                v___x_2161_ = crate::leanh::lean_box(0);
                                v___x_2162_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
                                if v_isShared_2111_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2162_);
                                    v___x_2164_ = v___x_2110_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2165_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2165_,
                                        0,
                                        v___x_2162_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2165_,
                                        1,
                                        v_snd_2108_,
                                    );
                                    v___x_2164_ = v_reuseFailAlloc_2165_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_g_2075_);
                v___x_2116_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_d_2113_, v___y_2115_, v_snd_2108_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                if crate::leanh::lean_obj_tag(v___x_2116_) == 0 {
                    v_a_2117_ = crate::leanh::lean_ctor_get(v___x_2116_, 0);
                    crate::leanh::lean_inc(v_a_2117_);
                    v_fst_2118_ = crate::leanh::lean_ctor_get(v_a_2117_, 0);
                    if crate::leanh::lean_obj_tag(v_fst_2118_) == 0 {
                        crate::leanh::lean_dec(v_a_2117_);
                        crate::leanh::lean_dec_ref(v_b_2114_);
                        crate::leanh::lean_dec_ref(v_g_2075_);
                        v___y_2097_ = v___x_2116_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2116_, 1);
                        v_snd_2119_ = crate::leanh::lean_ctor_get(v_a_2117_, 1);
                        crate::leanh::lean_inc(v_snd_2119_);
                        crate::leanh::lean_dec(v_a_2117_);
                        v___x_2120_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2075_, v_b_2114_, v___y_2115_, v_snd_2119_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
                        v___y_2097_ = v___x_2120_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2114_);
                    crate::leanh::lean_dec_ref(v_g_2075_);
                    v___y_2097_ = v___x_2116_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___x_2122_);
                if v_isShared_2106_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2105_, 0, v___x_2122_);
                    v___x_2124_ = v___x_2105_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
                    v___x_2124_ = v_reuseFailAlloc_2125_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___y_2092_ = v___x_2124_;
                v_a_2093_ = v___x_2122_;
                v_fst_2094_ = v___x_2101_;
                state = 2;
                continue;
            }
            9 => {
                v_a_2085_ = v___x_2132_;
                v_val_2086_ = v___x_2129_;
                state = 1;
                continue;
            }
            10 => {
                v_a_2085_ = v___x_2164_;
                v_val_2086_ = v___x_2161_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_2171_ == 0 {
                    v___x_2173_ = v___x_2170_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
                    v___x_2173_ = v_reuseFailAlloc_2174_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2173_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___boxed(
    mut v_g_2178_: *mut crate::leanh::LeanObject,
    mut v_e_2179_: *mut crate::leanh::LeanObject,
    mut v_a_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v_g_2178_, v_e_2179_, v_a_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
    crate::leanh::lean_dec(v___y_2185_);
    crate::leanh::lean_dec_ref(v___y_2184_);
    crate::leanh::lean_dec(v___y_2183_);
    crate::leanh::lean_dec_ref(v___y_2182_);
    crate::leanh::lean_dec(v_a_2180_);
    return v_res_2187_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(
    mut v_m_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
    mut v_b_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u64 = 0;
    let mut v___x_2195_: u64 = 0;
    let mut v___x_2196_: u64 = 0;
    let mut v_fold_2197_: u64 = 0;
    let mut v___x_2198_: u64 = 0;
    let mut v___x_2199_: u64 = 0;
    let mut v___x_2200_: u64 = 0;
    let mut v___x_2201_: usize = 0;
    let mut v___x_2202_: usize = 0;
    let mut v___x_2203_: usize = 0;
    let mut v___x_2204_: usize = 0;
    let mut v___x_2205_: usize = 0;
    let mut v_bkt_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: u8 = 0;
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: u8 = 0;
    let mut v_val_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_unused_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2191_ = crate::leanh::lean_ctor_get(v_m_2188_, 0);
                v_buckets_2192_ = crate::leanh::lean_ctor_get(v_m_2188_, 1);
                v___x_2193_ = lean_array_get_size(v_buckets_2192_);
                v___x_2194_ = l_Lean_Expr_hash(v_a_2189_);
                v___x_2195_ = 32u64;
                v___x_2196_ = lean_uint64_shift_right(v___x_2194_, v___x_2195_);
                v_fold_2197_ = lean_uint64_xor(v___x_2194_, v___x_2196_);
                v___x_2198_ = 16u64;
                v___x_2199_ = lean_uint64_shift_right(v_fold_2197_, v___x_2198_);
                v___x_2200_ = lean_uint64_xor(v_fold_2197_, v___x_2199_);
                v___x_2201_ = lean_uint64_to_usize(v___x_2200_);
                v___x_2202_ = lean_usize_of_nat(v___x_2193_);
                v___x_2203_ = 1usize;
                v___x_2204_ = lean_usize_sub(v___x_2202_, v___x_2203_);
                v___x_2205_ = lean_usize_land(v___x_2201_, v___x_2204_);
                v_bkt_2206_ = lean_array_uget_borrowed(v_buckets_2192_, v___x_2205_);
                v___x_2207_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(v_a_2189_, v_bkt_2206_);
                if v___x_2207_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2192_);
                    crate::leanh::lean_inc(v_size_2191_);
                    v_isSharedCheck_2228_ = (!crate::leanh::lean_is_exclusive(v_m_2188_)) as u8;
                    if v_isSharedCheck_2228_ == 0 {
                        v_unused_2229_ = crate::leanh::lean_ctor_get(v_m_2188_, 1);
                        crate::leanh::lean_dec(v_unused_2229_);
                        v_unused_2230_ = crate::leanh::lean_ctor_get(v_m_2188_, 0);
                        crate::leanh::lean_dec(v_unused_2230_);
                        v___x_2209_ = v_m_2188_;
                        v_isShared_2210_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2188_);
                        v___x_2209_ = crate::leanh::lean_box(0);
                        v_isShared_2210_ = v_isSharedCheck_2228_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2190_);
                    crate::leanh::lean_dec_ref(v_a_2189_);
                    return v_m_2188_;
                }
            }
            1 => {
                v___x_2211_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2212_ = lean_nat_add(v_size_2191_, v___x_2211_);
                crate::leanh::lean_dec(v_size_2191_);
                crate::leanh::lean_inc(v_bkt_2206_);
                v___x_2213_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2213_, 0, v_a_2189_);
                crate::leanh::lean_ctor_set(v___x_2213_, 1, v_b_2190_);
                crate::leanh::lean_ctor_set(v___x_2213_, 2, v_bkt_2206_);
                v_buckets_x27_2214_ = lean_array_uset(v_buckets_2192_, v___x_2205_, v___x_2213_);
                v___x_2215_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2216_ = lean_nat_mul(v_size_x27_2212_, v___x_2215_);
                v___x_2217_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2218_ = lean_nat_div(v___x_2216_, v___x_2217_);
                crate::leanh::lean_dec(v___x_2216_);
                v___x_2219_ = lean_array_get_size(v_buckets_x27_2214_);
                v___x_2220_ = lean_nat_dec_le(v___x_2218_, v___x_2219_);
                crate::leanh::lean_dec(v___x_2218_);
                if v___x_2220_ == 0 {
                    v_val_2221_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(v_buckets_x27_2214_);
                    if v_isShared_2210_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2209_, 1, v_val_2221_);
                        crate::leanh::lean_ctor_set(v___x_2209_, 0, v_size_x27_2212_);
                        v___x_2223_ = v___x_2209_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_size_x27_2212_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_val_2221_);
                        v___x_2223_ = v_reuseFailAlloc_2224_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2210_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2209_, 1, v_buckets_x27_2214_);
                        crate::leanh::lean_ctor_set(v___x_2209_, 0, v_size_x27_2212_);
                        v___x_2226_ = v___x_2209_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_size_x27_2212_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_buckets_x27_2214_);
                        v___x_2226_ = v_reuseFailAlloc_2227_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2223_;
            }
            3 => {
                return v___x_2226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(
    mut v_m_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u64 = 0;
    let mut v___x_2236_: u64 = 0;
    let mut v___x_2237_: u64 = 0;
    let mut v_fold_2238_: u64 = 0;
    let mut v___x_2239_: u64 = 0;
    let mut v___x_2240_: u64 = 0;
    let mut v___x_2241_: u64 = 0;
    let mut v___x_2242_: usize = 0;
    let mut v___x_2243_: usize = 0;
    let mut v___x_2244_: usize = 0;
    let mut v___x_2245_: usize = 0;
    let mut v___x_2246_: usize = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: u8 = 0;
    v_buckets_2233_ = crate::leanh::lean_ctor_get(v_m_2231_, 1);
    v___x_2234_ = lean_array_get_size(v_buckets_2233_);
    v___x_2235_ = l_Lean_Expr_hash(v_a_2232_);
    v___x_2236_ = 32u64;
    v___x_2237_ = lean_uint64_shift_right(v___x_2235_, v___x_2236_);
    v_fold_2238_ = lean_uint64_xor(v___x_2235_, v___x_2237_);
    v___x_2239_ = 16u64;
    v___x_2240_ = lean_uint64_shift_right(v_fold_2238_, v___x_2239_);
    v___x_2241_ = lean_uint64_xor(v_fold_2238_, v___x_2240_);
    v___x_2242_ = lean_uint64_to_usize(v___x_2241_);
    v___x_2243_ = lean_usize_of_nat(v___x_2234_);
    v___x_2244_ = 1usize;
    v___x_2245_ = lean_usize_sub(v___x_2243_, v___x_2244_);
    v___x_2246_ = lean_usize_land(v___x_2242_, v___x_2245_);
    v___x_2247_ = lean_array_uget_borrowed(v_buckets_2233_, v___x_2246_);
    v___x_2248_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(v_a_2232_, v___x_2247_);
    return v___x_2248_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg___boxed(
    mut v_m_2249_: *mut crate::leanh::LeanObject,
    mut v_a_2250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2251_: u8 = 0;
    let mut v_r_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2251_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(v_m_2249_, v_a_2250_);
    crate::leanh::lean_dec_ref(v_a_2250_);
    crate::leanh::lean_dec_ref(v_m_2249_);
    v_r_2252_ = crate::leanh::lean_box((v_res_2251_) as usize);
    return v_r_2252_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2253_ = crate::leanh::lean_box(0);
    v___x_2254_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2255_ = lean_mk_array(v___x_2254_, v___x_2253_);
    return v___x_2255_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__0);
    v___x_2257_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2258_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2258_, 0, v___x_2257_);
    crate::leanh::lean_ctor_set(v___x_2258_, 1, v___x_2256_);
    return v___x_2258_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0___boxed(
    mut v_ms_2259_: *mut crate::leanh::LeanObject,
    mut v_e_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
    mut v___y_2262_: *mut crate::leanh::LeanObject,
    mut v___y_2263_: *mut crate::leanh::LeanObject,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2267_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0(v_ms_2259_, v_e_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
    crate::leanh::lean_dec(v___y_2265_);
    crate::leanh::lean_dec_ref(v___y_2264_);
    crate::leanh::lean_dec(v___y_2263_);
    crate::leanh::lean_dec_ref(v___y_2262_);
    return v_res_2267_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(
    mut v_ms_2268_: *mut crate::leanh::LeanObject,
    mut v_m_2269_: *mut crate::leanh::LeanObject,
    mut v_a_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
    mut v_a_2272_: *mut crate::leanh::LeanObject,
    mut v_a_2273_: *mut crate::leanh::LeanObject,
    mut v_a_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2282_: u8 = 0;
    let mut v_fst_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2287_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_unused_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_unused_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2314_: u8 = 0;
    let mut v_a_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_a_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_2274_);
                crate::leanh::lean_inc_ref(v_a_2273_);
                crate::leanh::lean_inc(v_a_2272_);
                crate::leanh::lean_inc_ref(v_a_2271_);
                v___x_2276_ =
                    lean_infer_type(v_m_2269_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
                if crate::leanh::lean_obj_tag(v___x_2276_) == 0 {
                    v_a_2277_ = crate::leanh::lean_ctor_get(v___x_2276_, 0);
                    crate::leanh::lean_inc(v_a_2277_);
                    crate::leanh::lean_dec_ref_known(v___x_2276_, 1);
                    v___x_2278_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(v_a_2277_, v_a_2270_, v_a_2272_);
                    if crate::leanh::lean_obj_tag(v___x_2278_) == 0 {
                        v_a_2279_ = crate::leanh::lean_ctor_get(v___x_2278_, 0);
                        v_isSharedCheck_2314_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2278_)) as u8;
                        if v_isSharedCheck_2314_ == 0 {
                            v___x_2281_ = v___x_2278_;
                            v_isShared_2282_ = v_isSharedCheck_2314_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2279_);
                            crate::leanh::lean_dec(v___x_2278_);
                            v___x_2281_ = crate::leanh::lean_box(0);
                            v_isShared_2282_ = v_isSharedCheck_2314_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ms_2268_);
                        v_a_2315_ = crate::leanh::lean_ctor_get(v___x_2278_, 0);
                        v_isSharedCheck_2322_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2278_)) as u8;
                        if v_isSharedCheck_2322_ == 0 {
                            v___x_2317_ = v___x_2278_;
                            v_isShared_2318_ = v_isSharedCheck_2322_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2315_);
                            crate::leanh::lean_dec(v___x_2278_);
                            v___x_2317_ = crate::leanh::lean_box(0);
                            v_isShared_2318_ = v_isSharedCheck_2322_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2270_);
                    crate::leanh::lean_dec_ref(v_ms_2268_);
                    v_a_2323_ = crate::leanh::lean_ctor_get(v___x_2276_, 0);
                    v_isSharedCheck_2330_ = (!crate::leanh::lean_is_exclusive(v___x_2276_)) as u8;
                    if v_isSharedCheck_2330_ == 0 {
                        v___x_2325_ = v___x_2276_;
                        v_isShared_2326_ = v_isSharedCheck_2330_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2323_);
                        crate::leanh::lean_dec(v___x_2276_);
                        v___x_2325_ = crate::leanh::lean_box(0);
                        v_isShared_2326_ = v_isSharedCheck_2330_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2283_ = crate::leanh::lean_ctor_get(v_a_2279_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2283_) == 0 {
                    crate::leanh::lean_dec_ref(v_ms_2268_);
                    v_snd_2284_ = crate::leanh::lean_ctor_get(v_a_2279_, 1);
                    v_isSharedCheck_2295_ = (!crate::leanh::lean_is_exclusive(v_a_2279_)) as u8;
                    if v_isSharedCheck_2295_ == 0 {
                        v_unused_2296_ = crate::leanh::lean_ctor_get(v_a_2279_, 0);
                        crate::leanh::lean_dec(v_unused_2296_);
                        v___x_2286_ = v_a_2279_;
                        v_isShared_2287_ = v_isSharedCheck_2295_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2284_);
                        crate::leanh::lean_dec(v_a_2279_);
                        v___x_2286_ = crate::leanh::lean_box(0);
                        v_isShared_2287_ = v_isSharedCheck_2295_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2283_);
                    crate::leanh::lean_del_object(v___x_2281_);
                    v_snd_2297_ = crate::leanh::lean_ctor_get(v_a_2279_, 1);
                    crate::leanh::lean_inc(v_snd_2297_);
                    crate::leanh::lean_dec(v_a_2279_);
                    v_val_2298_ = crate::leanh::lean_ctor_get(v_fst_2283_, 0);
                    crate::leanh::lean_inc(v_val_2298_);
                    crate::leanh::lean_dec_ref_known(v_fst_2283_, 1);
                    v___x_2299_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1);
                    v___x_2300_ = lean_st_mk_ref(v___x_2299_);
                    v___f_2301_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___f_2301_, 0, v_ms_2268_);
                    v___x_2302_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5(v___f_2301_, v_val_2298_, v___x_2300_, v_snd_2297_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
                    if crate::leanh::lean_obj_tag(v___x_2302_) == 0 {
                        v_a_2303_ = crate::leanh::lean_ctor_get(v___x_2302_, 0);
                        crate::leanh::lean_inc(v_a_2303_);
                        v_fst_2304_ = crate::leanh::lean_ctor_get(v_a_2303_, 0);
                        if crate::leanh::lean_obj_tag(v_fst_2304_) == 0 {
                            crate::leanh::lean_dec(v_a_2303_);
                            crate::leanh::lean_dec(v___x_2300_);
                            return v___x_2302_;
                        } else {
                            v_isSharedCheck_2312_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2302_)) as u8;
                            if v_isSharedCheck_2312_ == 0 {
                                v_unused_2313_ = crate::leanh::lean_ctor_get(v___x_2302_, 0);
                                crate::leanh::lean_dec(v_unused_2313_);
                                v___x_2306_ = v___x_2302_;
                                v_isShared_2307_ = v_isSharedCheck_2312_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2302_);
                                v___x_2306_ = crate::leanh::lean_box(0);
                                v_isShared_2307_ = v_isSharedCheck_2312_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2300_);
                        return v___x_2302_;
                    }
                }
            }
            2 => {
                v___x_2288_ = crate::leanh::lean_box(0);
                if v_isShared_2287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2286_, 0, v___x_2288_);
                    v___x_2290_ = v___x_2286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2294_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_snd_2284_);
                    v___x_2290_ = v_reuseFailAlloc_2294_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2282_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2281_, 0, v___x_2290_);
                    v___x_2292_ = v___x_2281_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2293_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2290_);
                    v___x_2292_ = v_reuseFailAlloc_2293_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2292_;
            }
            5 => {
                v___x_2308_ = lean_st_ref_get(v___x_2300_);
                crate::leanh::lean_dec(v___x_2300_);
                crate::leanh::lean_dec(v___x_2308_);
                if v_isShared_2307_ == 0 {
                    v___x_2310_ = v___x_2306_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2303_);
                    v___x_2310_ = v_reuseFailAlloc_2311_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2310_;
            }
            7 => {
                if v_isShared_2318_ == 0 {
                    v___x_2320_ = v___x_2317_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
                    v___x_2320_ = v_reuseFailAlloc_2321_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2320_;
            }
            9 => {
                if v_isShared_2326_ == 0 {
                    v___x_2328_ = v___x_2325_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(
    mut v_ms_2331_: *mut crate::leanh::LeanObject,
    mut v_m_2332_: *mut crate::leanh::LeanObject,
    mut v_a_2333_: *mut crate::leanh::LeanObject,
    mut v_a_2334_: *mut crate::leanh::LeanObject,
    mut v_a_2335_: *mut crate::leanh::LeanObject,
    mut v_a_2336_: *mut crate::leanh::LeanObject,
    mut v_a_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tempMark_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_permMark_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: u8 = 0;
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v_snd_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v_tempMark_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_permMark_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_unused_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut v_unused_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2385_: u8 = 0;
    let mut v_unused_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_tempMark_2339_ = crate::leanh::lean_ctor_get(v_a_2333_, 0);
                v_permMark_2340_ = crate::leanh::lean_ctor_get(v_a_2333_, 1);
                v_result_2341_ = crate::leanh::lean_ctor_get(v_a_2333_, 2);
                v___x_2342_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(v_permMark_2340_, v_m_2332_);
                if v___x_2342_ == 0 {
                    v___x_2343_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(v_tempMark_2339_, v_m_2332_);
                    if v___x_2343_ == 0 {
                        crate::leanh::lean_inc_ref(v_result_2341_);
                        crate::leanh::lean_inc_ref(v_permMark_2340_);
                        crate::leanh::lean_inc_ref(v_tempMark_2339_);
                        v_isSharedCheck_2385_ = (!crate::leanh::lean_is_exclusive(v_a_2333_)) as u8;
                        if v_isSharedCheck_2385_ == 0 {
                            v_unused_2386_ = crate::leanh::lean_ctor_get(v_a_2333_, 2);
                            crate::leanh::lean_dec(v_unused_2386_);
                            v_unused_2387_ = crate::leanh::lean_ctor_get(v_a_2333_, 1);
                            crate::leanh::lean_dec(v_unused_2387_);
                            v_unused_2388_ = crate::leanh::lean_ctor_get(v_a_2333_, 0);
                            crate::leanh::lean_dec(v_unused_2388_);
                            v___x_2345_ = v_a_2333_;
                            v_isShared_2346_ = v_isSharedCheck_2385_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2333_);
                            v___x_2345_ = crate::leanh::lean_box(0);
                            v_isShared_2346_ = v_isSharedCheck_2385_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_m_2332_);
                        crate::leanh::lean_dec_ref(v_ms_2331_);
                        v___x_2389_ = crate::leanh::lean_box(0);
                        v___x_2390_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2390_, 0, v___x_2389_);
                        crate::leanh::lean_ctor_set(v___x_2390_, 1, v_a_2333_);
                        v___x_2391_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2391_, 0, v___x_2390_);
                        return v___x_2391_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_m_2332_);
                    crate::leanh::lean_dec_ref(v_ms_2331_);
                    v___x_2392_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
                    v___x_2393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2393_, 0, v___x_2392_);
                    crate::leanh::lean_ctor_set(v___x_2393_, 1, v_a_2333_);
                    v___x_2394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2394_, 0, v___x_2393_);
                    return v___x_2394_;
                }
            }
            1 => {
                v___x_2347_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_m_2332_);
                v___x_2348_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(v_tempMark_2339_, v_m_2332_, v___x_2347_);
                if v_isShared_2346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2345_, 0, v___x_2348_);
                    v___x_2350_ = v___x_2345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_permMark_2340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_result_2341_);
                    v___x_2350_ = v_reuseFailAlloc_2384_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_m_2332_);
                v___x_2351_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(v_ms_2331_, v_m_2332_, v___x_2350_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
                if crate::leanh::lean_obj_tag(v___x_2351_) == 0 {
                    v_a_2352_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                    crate::leanh::lean_inc(v_a_2352_);
                    v_fst_2353_ = crate::leanh::lean_ctor_get(v_a_2352_, 0);
                    if crate::leanh::lean_obj_tag(v_fst_2353_) == 0 {
                        crate::leanh::lean_dec(v_a_2352_);
                        crate::leanh::lean_dec_ref(v_m_2332_);
                        return v___x_2351_;
                    } else {
                        v_isSharedCheck_2382_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                        if v_isSharedCheck_2382_ == 0 {
                            v_unused_2383_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                            crate::leanh::lean_dec(v_unused_2383_);
                            v___x_2355_ = v___x_2351_;
                            v_isShared_2356_ = v_isSharedCheck_2382_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2351_);
                            v___x_2355_ = crate::leanh::lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2382_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_m_2332_);
                    return v___x_2351_;
                }
            }
            3 => {
                v_snd_2357_ = crate::leanh::lean_ctor_get(v_a_2352_, 1);
                v_isSharedCheck_2380_ = (!crate::leanh::lean_is_exclusive(v_a_2352_)) as u8;
                if v_isSharedCheck_2380_ == 0 {
                    v_unused_2381_ = crate::leanh::lean_ctor_get(v_a_2352_, 0);
                    crate::leanh::lean_dec(v_unused_2381_);
                    v___x_2359_ = v_a_2352_;
                    v_isShared_2360_ = v_isSharedCheck_2380_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2357_);
                    crate::leanh::lean_dec(v_a_2352_);
                    v___x_2359_ = crate::leanh::lean_box(0);
                    v_isShared_2360_ = v_isSharedCheck_2380_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_tempMark_2361_ = crate::leanh::lean_ctor_get(v_snd_2357_, 0);
                v_permMark_2362_ = crate::leanh::lean_ctor_get(v_snd_2357_, 1);
                v_result_2363_ = crate::leanh::lean_ctor_get(v_snd_2357_, 2);
                v_isSharedCheck_2379_ = (!crate::leanh::lean_is_exclusive(v_snd_2357_)) as u8;
                if v_isSharedCheck_2379_ == 0 {
                    v___x_2365_ = v_snd_2357_;
                    v_isShared_2366_ = v_isSharedCheck_2379_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_result_2363_);
                    crate::leanh::lean_inc(v_permMark_2362_);
                    crate::leanh::lean_inc(v_tempMark_2361_);
                    crate::leanh::lean_dec(v_snd_2357_);
                    v___x_2365_ = crate::leanh::lean_box(0);
                    v_isShared_2366_ = v_isSharedCheck_2379_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v_m_2332_);
                v___x_2367_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(v_permMark_2362_, v_m_2332_, v___x_2347_);
                v___x_2368_ = lean_array_push(v_result_2363_, v_m_2332_);
                if v_isShared_2366_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2365_, 2, v___x_2368_);
                    crate::leanh::lean_ctor_set(v___x_2365_, 1, v___x_2367_);
                    v___x_2370_ = v___x_2365_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_tempMark_2361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 1, v___x_2367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 2, v___x_2368_);
                    v___x_2370_ = v_reuseFailAlloc_2378_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2371_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
                if v_isShared_2360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2359_, 1, v___x_2370_);
                    crate::leanh::lean_ctor_set(v___x_2359_, 0, v___x_2371_);
                    v___x_2373_ = v___x_2359_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2370_);
                    v___x_2373_ = v_reuseFailAlloc_2377_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2356_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2373_);
                    v___x_2375_ = v___x_2355_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
                    v___x_2375_ = v_reuseFailAlloc_2376_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___lam__0(
    mut v_ms_2395_: *mut crate::leanh::LeanObject,
    mut v_e_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2403_: u8 = 0;
    let mut v___y_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2411_: u8 = 0;
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2416_: u8 = 0;
    let mut v_fst_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v_unused_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut v_a_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2436_: u8 = 0;
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2403_ = l_Lean_Expr_hasExprMVar(v_e_2396_);
                if v___x_2403_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2396_);
                    crate::leanh::lean_dec_ref(v_ms_2395_);
                    v___x_2441_ = crate::leanh::lean_box((v___x_2403_) as usize);
                    v___x_2442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2442_, 0, v___x_2441_);
                    v___x_2443_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2442_);
                    crate::leanh::lean_ctor_set(v___x_2443_, 1, v___y_2397_);
                    v___x_2444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2444_, 0, v___x_2443_);
                    return v___x_2444_;
                } else {
                    v___x_2445_ = l_Lean_Expr_isMVar(v_e_2396_);
                    if v___x_2445_ == 0 {
                        v___y_2411_ = v___x_2445_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2446_ = l_Array_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__3(v_ms_2395_, v_e_2396_);
                        v___y_2411_ = v___x_2446_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2406_ = crate::leanh::lean_box((v___x_2403_) as usize);
                v___x_2407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2407_, 0, v___x_2406_);
                v___x_2408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2408_, 0, v___x_2407_);
                crate::leanh::lean_ctor_set(v___x_2408_, 1, v___y_2405_);
                v___x_2409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2409_, 0, v___x_2408_);
                return v___x_2409_;
            }
            2 => {
                if v___y_2411_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2396_);
                    crate::leanh::lean_dec_ref(v_ms_2395_);
                    v___y_2405_ = v___y_2397_;
                    state = 1;
                    continue;
                } else {
                    v___x_2412_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(v_ms_2395_, v_e_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
                    if crate::leanh::lean_obj_tag(v___x_2412_) == 0 {
                        v_a_2413_ = crate::leanh::lean_ctor_get(v___x_2412_, 0);
                        v_isSharedCheck_2432_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2412_)) as u8;
                        if v_isSharedCheck_2432_ == 0 {
                            v___x_2415_ = v___x_2412_;
                            v_isShared_2416_ = v_isSharedCheck_2432_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2413_);
                            crate::leanh::lean_dec(v___x_2412_);
                            v___x_2415_ = crate::leanh::lean_box(0);
                            v_isShared_2416_ = v_isSharedCheck_2432_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2433_ = crate::leanh::lean_ctor_get(v___x_2412_, 0);
                        v_isSharedCheck_2440_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2412_)) as u8;
                        if v_isSharedCheck_2440_ == 0 {
                            v___x_2435_ = v___x_2412_;
                            v_isShared_2436_ = v_isSharedCheck_2440_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2433_);
                            crate::leanh::lean_dec(v___x_2412_);
                            v___x_2435_ = crate::leanh::lean_box(0);
                            v_isShared_2436_ = v_isSharedCheck_2440_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_fst_2417_ = crate::leanh::lean_ctor_get(v_a_2413_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2417_) == 0 {
                    v_snd_2418_ = crate::leanh::lean_ctor_get(v_a_2413_, 1);
                    v_isSharedCheck_2429_ = (!crate::leanh::lean_is_exclusive(v_a_2413_)) as u8;
                    if v_isSharedCheck_2429_ == 0 {
                        v_unused_2430_ = crate::leanh::lean_ctor_get(v_a_2413_, 0);
                        crate::leanh::lean_dec(v_unused_2430_);
                        v___x_2420_ = v_a_2413_;
                        v_isShared_2421_ = v_isSharedCheck_2429_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2418_);
                        crate::leanh::lean_dec(v_a_2413_);
                        v___x_2420_ = crate::leanh::lean_box(0);
                        v_isShared_2421_ = v_isSharedCheck_2429_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2415_);
                    v_snd_2431_ = crate::leanh::lean_ctor_get(v_a_2413_, 1);
                    crate::leanh::lean_inc(v_snd_2431_);
                    crate::leanh::lean_dec(v_a_2413_);
                    v___y_2405_ = v_snd_2431_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_2422_ = crate::leanh::lean_box(0);
                if v_isShared_2421_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2420_, 0, v___x_2422_);
                    v___x_2424_ = v___x_2420_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_snd_2418_);
                    v___x_2424_ = v_reuseFailAlloc_2428_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2416_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2415_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2415_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2426_;
            }
            7 => {
                if v_isShared_2436_ == 0 {
                    v___x_2438_ = v___x_2435_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
                    v___x_2438_ = v_reuseFailAlloc_2439_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit___boxed(
    mut v_ms_2447_: *mut crate::leanh::LeanObject,
    mut v_m_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
    mut v_a_2451_: *mut crate::leanh::LeanObject,
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_a_2453_: *mut crate::leanh::LeanObject,
    mut v_a_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2455_ =
        l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(
            v_ms_2447_, v_m_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_,
        );
    crate::leanh::lean_dec(v_a_2453_);
    crate::leanh::lean_dec_ref(v_a_2452_);
    crate::leanh::lean_dec(v_a_2451_);
    crate::leanh::lean_dec_ref(v_a_2450_);
    return v_res_2455_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___boxed(
    mut v_ms_2456_: *mut crate::leanh::LeanObject,
    mut v_m_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
    mut v_a_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2464_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf(v_ms_2456_, v_m_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
    crate::leanh::lean_dec(v_a_2462_);
    crate::leanh::lean_dec_ref(v_a_2461_);
    crate::leanh::lean_dec(v_a_2460_);
    crate::leanh::lean_dec_ref(v_a_2459_);
    return v_res_2464_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4(
    mut v_e_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
    mut v___y_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___redArg(v_e_2465_, v___y_2466_, v___y_2468_);
    return v___x_2472_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4___boxed(
    mut v_e_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2480_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__4(v_e_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
    crate::leanh::lean_dec(v___y_2478_);
    crate::leanh::lean_dec_ref(v___y_2477_);
    crate::leanh::lean_dec(v___y_2476_);
    crate::leanh::lean_dec_ref(v___y_2475_);
    return v_res_2480_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0(
    mut v_00_u03b2_2481_: *mut crate::leanh::LeanObject,
    mut v_m_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2484_: u8 = 0;
    v___x_2484_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___redArg(v_m_2482_, v_a_2483_);
    return v___x_2484_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0___boxed(
    mut v_00_u03b2_2485_: *mut crate::leanh::LeanObject,
    mut v_m_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2488_: u8 = 0;
    let mut v_r_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2488_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0(v_00_u03b2_2485_, v_m_2486_, v_a_2487_);
    crate::leanh::lean_dec_ref(v_a_2487_);
    crate::leanh::lean_dec_ref(v_m_2486_);
    v_r_2489_ = crate::leanh::lean_box((v_res_2488_) as usize);
    return v_r_2489_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1(
    mut v_00_u03b2_2490_: *mut crate::leanh::LeanObject,
    mut v_m_2491_: *mut crate::leanh::LeanObject,
    mut v_a_2492_: *mut crate::leanh::LeanObject,
    mut v_b_2493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1___redArg(v_m_2491_, v_a_2492_, v_b_2493_);
    return v___x_2494_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0(
    mut v_00_u03b2_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_x_2497_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2498_: u8 = 0;
    v___x_2498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___redArg(v_a_2496_, v_x_2497_);
    return v___x_2498_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0___boxed(
    mut v_00_u03b2_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
    mut v_x_2501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2502_: u8 = 0;
    let mut v_r_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2502_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__0_spec__0(v_00_u03b2_2499_, v_a_2500_, v_x_2501_);
    crate::leanh::lean_dec(v_x_2501_);
    crate::leanh::lean_dec_ref(v_a_2500_);
    v_r_2503_ = crate::leanh::lean_box((v_res_2502_) as usize);
    return v_r_2503_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2(
    mut v_00_u03b2_2504_: *mut crate::leanh::LeanObject,
    mut v_data_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2506_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2___redArg(v_data_2505_);
    return v___x_2506_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8(
    mut v_00_u03b2_2507_: *mut crate::leanh::LeanObject,
    mut v_m_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___redArg(v_m_2508_, v_a_2509_);
    return v___x_2510_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8___boxed(
    mut v_00_u03b2_2511_: *mut crate::leanh::LeanObject,
    mut v_m_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8(v_00_u03b2_2511_, v_m_2512_, v_a_2513_);
    crate::leanh::lean_dec_ref(v_a_2513_);
    crate::leanh::lean_dec_ref(v_m_2512_);
    return v_res_2514_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9(
    mut v_00_u03b2_2515_: *mut crate::leanh::LeanObject,
    mut v_m_2516_: *mut crate::leanh::LeanObject,
    mut v_a_2517_: *mut crate::leanh::LeanObject,
    mut v_b_2518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2519_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9___redArg(v_m_2516_, v_a_2517_, v_b_2518_);
    return v___x_2519_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2520_: *mut crate::leanh::LeanObject,
    mut v_i_2521_: *mut crate::leanh::LeanObject,
    mut v_source_2522_: *mut crate::leanh::LeanObject,
    mut v_target_2523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2524_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5___redArg(v_i_2521_, v_source_2522_, v_target_2523_);
    return v___x_2524_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10(
    mut v_00_u03b2_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
    mut v_x_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___redArg(v_a_2526_, v_x_2527_);
    return v___x_2528_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10___boxed(
    mut v_00_u03b2_2529_: *mut crate::leanh::LeanObject,
    mut v_a_2530_: *mut crate::leanh::LeanObject,
    mut v_x_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2532_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__8_spec__10(v_00_u03b2_2529_, v_a_2530_, v_x_2531_);
    crate::leanh::lean_dec(v_x_2531_);
    crate::leanh::lean_dec_ref(v_a_2530_);
    return v_res_2532_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12(
    mut v_00_u03b2_2533_: *mut crate::leanh::LeanObject,
    mut v_a_2534_: *mut crate::leanh::LeanObject,
    mut v_b_2535_: *mut crate::leanh::LeanObject,
    mut v_x_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2537_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5_spec__9_spec__12___redArg(v_a_2534_, v_b_2535_, v_x_2536_);
    return v___x_2537_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8(
    mut v_00_u03b2_2538_: *mut crate::leanh::LeanObject,
    mut v_x_2539_: *mut crate::leanh::LeanObject,
    mut v_x_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit_spec__1_spec__2_spec__5_spec__8___redArg(v_x_2539_, v_x_2540_);
    return v___x_2541_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(
    mut v_ms_2542_: *mut crate::leanh::LeanObject,
    mut v_as_2543_: *mut crate::leanh::LeanObject,
    mut v_sz_2544_: usize,
    mut v_i_2545_: usize,
    mut v_b_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: usize = 0;
    let mut v___x_2564_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2553_ = lean_usize_dec_lt(v_i_2545_, v_sz_2544_);
                if v___x_2553_ == 0 {
                    crate::leanh::lean_dec_ref(v_ms_2542_);
                    v___x_2554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2554_, 0, v_b_2546_);
                    v___x_2555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2554_);
                    crate::leanh::lean_ctor_set(v___x_2555_, 1, v___y_2547_);
                    v___x_2556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2556_, 0, v___x_2555_);
                    return v___x_2556_;
                } else {
                    v_a_2557_ = lean_array_uget_borrowed(v_as_2543_, v_i_2545_);
                    crate::leanh::lean_inc(v_a_2557_);
                    crate::leanh::lean_inc_ref(v_ms_2542_);
                    v___x_2558_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visit(v_ms_2542_, v_a_2557_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
                    if crate::leanh::lean_obj_tag(v___x_2558_) == 0 {
                        v_a_2559_ = crate::leanh::lean_ctor_get(v___x_2558_, 0);
                        crate::leanh::lean_inc(v_a_2559_);
                        v_fst_2560_ = crate::leanh::lean_ctor_get(v_a_2559_, 0);
                        if crate::leanh::lean_obj_tag(v_fst_2560_) == 0 {
                            crate::leanh::lean_dec(v_a_2559_);
                            crate::leanh::lean_dec_ref(v_ms_2542_);
                            return v___x_2558_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2558_, 1);
                            v_snd_2561_ = crate::leanh::lean_ctor_get(v_a_2559_, 1);
                            crate::leanh::lean_inc(v_snd_2561_);
                            crate::leanh::lean_dec(v_a_2559_);
                            v___x_2562_ = crate::leanh::lean_box(0);
                            v___x_2563_ = 1usize;
                            v___x_2564_ = lean_usize_add(v_i_2545_, v___x_2563_);
                            v_i_2545_ = v___x_2564_;
                            v_b_2546_ = v___x_2562_;
                            v___y_2547_ = v_snd_2561_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_ms_2542_);
                        return v___x_2558_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0___boxed(
    mut v_ms_2566_: *mut crate::leanh::LeanObject,
    mut v_as_2567_: *mut crate::leanh::LeanObject,
    mut v_sz_2568_: *mut crate::leanh::LeanObject,
    mut v_i_2569_: *mut crate::leanh::LeanObject,
    mut v_b_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2577_: usize = 0;
    let mut v_i_boxed_2578_: usize = 0;
    let mut v_res_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2577_ = crate::leanh::lean_unbox_usize(v_sz_2568_);
    crate::leanh::lean_dec(v_sz_2568_);
    v_i_boxed_2578_ = crate::leanh::lean_unbox_usize(v_i_2569_);
    crate::leanh::lean_dec(v_i_2569_);
    v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(v_ms_2566_, v_as_2567_, v_sz_boxed_2577_, v_i_boxed_2578_, v_b_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
    crate::leanh::lean_dec(v___y_2575_);
    crate::leanh::lean_dec_ref(v___y_2574_);
    crate::leanh::lean_dec(v___y_2573_);
    crate::leanh::lean_dec_ref(v___y_2572_);
    crate::leanh::lean_dec_ref(v_as_2567_);
    return v_res_2579_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(
    mut v_ms_2580_: *mut crate::leanh::LeanObject,
    mut v_a_2581_: *mut crate::leanh::LeanObject,
    mut v_a_2582_: *mut crate::leanh::LeanObject,
    mut v_a_2583_: *mut crate::leanh::LeanObject,
    mut v_a_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2588_: usize = 0;
    let mut v___x_2589_: usize = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2595_: u8 = 0;
    let mut v_snd_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v_unused_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut v_unused_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2587_ = crate::leanh::lean_box(0);
                v_sz_2588_ = lean_array_size(v_ms_2580_);
                v___x_2589_ = 0usize;
                crate::leanh::lean_inc_ref(v_ms_2580_);
                v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go_spec__0(v_ms_2580_, v_ms_2580_, v_sz_2588_, v___x_2589_, v___x_2587_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_);
                crate::leanh::lean_dec_ref(v_ms_2580_);
                if crate::leanh::lean_obj_tag(v___x_2590_) == 0 {
                    v_a_2591_ = crate::leanh::lean_ctor_get(v___x_2590_, 0);
                    crate::leanh::lean_inc(v_a_2591_);
                    v_fst_2592_ = crate::leanh::lean_ctor_get(v_a_2591_, 0);
                    if crate::leanh::lean_obj_tag(v_fst_2592_) == 0 {
                        crate::leanh::lean_dec(v_a_2591_);
                        return v___x_2590_;
                    } else {
                        v_isSharedCheck_2609_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2590_)) as u8;
                        if v_isSharedCheck_2609_ == 0 {
                            v_unused_2610_ = crate::leanh::lean_ctor_get(v___x_2590_, 0);
                            crate::leanh::lean_dec(v_unused_2610_);
                            v___x_2594_ = v___x_2590_;
                            v_isShared_2595_ = v_isSharedCheck_2609_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2590_);
                            v___x_2594_ = crate::leanh::lean_box(0);
                            v_isShared_2595_ = v_isSharedCheck_2609_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_2590_;
                }
            }
            1 => {
                v_snd_2596_ = crate::leanh::lean_ctor_get(v_a_2591_, 1);
                v_isSharedCheck_2607_ = (!crate::leanh::lean_is_exclusive(v_a_2591_)) as u8;
                if v_isSharedCheck_2607_ == 0 {
                    v_unused_2608_ = crate::leanh::lean_ctor_get(v_a_2591_, 0);
                    crate::leanh::lean_dec(v_unused_2608_);
                    v___x_2598_ = v_a_2591_;
                    v_isShared_2599_ = v_isSharedCheck_2607_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2596_);
                    crate::leanh::lean_dec(v_a_2591_);
                    v___x_2598_ = crate::leanh::lean_box(0);
                    v_isShared_2599_ = v_isSharedCheck_2607_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2600_ = l_Lean_ForEachExpr_visit___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf_spec__5___closed__0;
                if v_isShared_2599_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2598_, 0, v___x_2600_);
                    v___x_2602_ = v___x_2598_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2600_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 1, v_snd_2596_);
                    v___x_2602_ = v_reuseFailAlloc_2606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2595_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2594_, 0, v___x_2602_);
                    v___x_2604_ = v___x_2594_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
                    v___x_2604_ = v_reuseFailAlloc_2605_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go___boxed(
    mut v_ms_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_a_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2618_ =
        l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(
            v_ms_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_,
        );
    crate::leanh::lean_dec(v_a_2616_);
    crate::leanh::lean_dec_ref(v_a_2615_);
    crate::leanh::lean_dec(v_a_2614_);
    crate::leanh::lean_dec_ref(v_a_2613_);
    return v_res_2618_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2621_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
    v___x_2622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_visitTypeOf___closed__1);
    v___x_2623_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2622_);
    crate::leanh::lean_ctor_set(v___x_2623_, 1, v___x_2622_);
    crate::leanh::lean_ctor_set(v___x_2623_, 2, v___x_2621_);
    return v___x_2623_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(
    mut v_ms_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v_fst_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v_snd_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_unused_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut v_a_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2630_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__1);
                v___x_2631_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f_go(v_ms_2624_, v___x_2630_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_);
                if crate::leanh::lean_obj_tag(v___x_2631_) == 0 {
                    v_a_2632_ = crate::leanh::lean_ctor_get(v___x_2631_, 0);
                    v_isSharedCheck_2654_ = (!crate::leanh::lean_is_exclusive(v___x_2631_)) as u8;
                    if v_isSharedCheck_2654_ == 0 {
                        v___x_2634_ = v___x_2631_;
                        v_isShared_2635_ = v_isSharedCheck_2654_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2632_);
                        crate::leanh::lean_dec(v___x_2631_);
                        v___x_2634_ = crate::leanh::lean_box(0);
                        v_isShared_2635_ = v_isSharedCheck_2654_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2655_ = crate::leanh::lean_ctor_get(v___x_2631_, 0);
                    v_isSharedCheck_2662_ = (!crate::leanh::lean_is_exclusive(v___x_2631_)) as u8;
                    if v_isSharedCheck_2662_ == 0 {
                        v___x_2657_ = v___x_2631_;
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2655_);
                        crate::leanh::lean_dec(v___x_2631_);
                        v___x_2657_ = crate::leanh::lean_box(0);
                        v_isShared_2658_ = v_isSharedCheck_2662_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2636_ = crate::leanh::lean_ctor_get(v_a_2632_, 0);
                crate::leanh::lean_inc(v_fst_2636_);
                if crate::leanh::lean_obj_tag(v_fst_2636_) == 1 {
                    v_isSharedCheck_2648_ = (!crate::leanh::lean_is_exclusive(v_fst_2636_)) as u8;
                    if v_isSharedCheck_2648_ == 0 {
                        v_unused_2649_ = crate::leanh::lean_ctor_get(v_fst_2636_, 0);
                        crate::leanh::lean_dec(v_unused_2649_);
                        v___x_2638_ = v_fst_2636_;
                        v_isShared_2639_ = v_isSharedCheck_2648_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_2636_);
                        v___x_2638_ = crate::leanh::lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2648_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_2636_);
                    crate::leanh::lean_dec(v_a_2632_);
                    v___x_2650_ = crate::leanh::lean_box(0);
                    if v_isShared_2635_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2650_);
                        v___x_2652_ = v___x_2634_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2650_);
                        v___x_2652_ = v_reuseFailAlloc_2653_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_2640_ = crate::leanh::lean_ctor_get(v_a_2632_, 1);
                crate::leanh::lean_inc(v_snd_2640_);
                crate::leanh::lean_dec(v_a_2632_);
                v_result_2641_ = crate::leanh::lean_ctor_get(v_snd_2640_, 2);
                crate::leanh::lean_inc_ref(v_result_2641_);
                crate::leanh::lean_dec(v_snd_2640_);
                if v_isShared_2639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2638_, 0, v_result_2641_);
                    v___x_2643_ = v___x_2638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2647_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_result_2641_);
                    v___x_2643_ = v_reuseFailAlloc_2647_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2643_);
                    v___x_2645_ = v___x_2634_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
                    v___x_2645_ = v_reuseFailAlloc_2646_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2645_;
            }
            5 => {
                return v___x_2652_;
            }
            6 => {
                if v_isShared_2658_ == 0 {
                    v___x_2660_ = v___x_2657_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2655_);
                    v___x_2660_ = v_reuseFailAlloc_2661_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___boxed(
    mut v_ms_2663_: *mut crate::leanh::LeanObject,
    mut v_a_2664_: *mut crate::leanh::LeanObject,
    mut v_a_2665_: *mut crate::leanh::LeanObject,
    mut v_a_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
    mut v_a_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2669_ =
        l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(
            v_ms_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_,
        );
    crate::leanh::lean_dec(v_a_2667_);
    crate::leanh::lean_dec_ref(v_a_2666_);
    crate::leanh::lean_dec(v_a_2665_);
    crate::leanh::lean_dec_ref(v_a_2664_);
    return v_res_2669_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(
    mut v_e_2670_: *mut crate::leanh::LeanObject,
    mut v___y_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_unused_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2673_ = l_Lean_Expr_hasMVar(v_e_2670_);
                if v___x_2673_ == 0 {
                    v___x_2674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2674_, 0, v_e_2670_);
                    return v___x_2674_;
                } else {
                    v___x_2675_ = lean_st_ref_get(v___y_2671_);
                    v_mctx_2676_ = crate::leanh::lean_ctor_get(v___x_2675_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2676_);
                    crate::leanh::lean_dec(v___x_2675_);
                    v___x_2677_ = l_Lean_instantiateMVarsCore(v_mctx_2676_, v_e_2670_);
                    v_fst_2678_ = crate::leanh::lean_ctor_get(v___x_2677_, 0);
                    crate::leanh::lean_inc(v_fst_2678_);
                    v_snd_2679_ = crate::leanh::lean_ctor_get(v___x_2677_, 1);
                    crate::leanh::lean_inc(v_snd_2679_);
                    crate::leanh::lean_dec_ref(v___x_2677_);
                    v___x_2680_ = lean_st_ref_take(v___y_2671_);
                    v_cache_2681_ = crate::leanh::lean_ctor_get(v___x_2680_, 1);
                    v_zetaDeltaFVarIds_2682_ = crate::leanh::lean_ctor_get(v___x_2680_, 2);
                    v_postponed_2683_ = crate::leanh::lean_ctor_get(v___x_2680_, 3);
                    v_diag_2684_ = crate::leanh::lean_ctor_get(v___x_2680_, 4);
                    v_isSharedCheck_2693_ = (!crate::leanh::lean_is_exclusive(v___x_2680_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v_unused_2694_ = crate::leanh::lean_ctor_get(v___x_2680_, 0);
                        crate::leanh::lean_dec(v_unused_2694_);
                        v___x_2686_ = v___x_2680_;
                        v_isShared_2687_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2684_);
                        crate::leanh::lean_inc(v_postponed_2683_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2682_);
                        crate::leanh::lean_inc(v_cache_2681_);
                        crate::leanh::lean_dec(v___x_2680_);
                        v___x_2686_ = crate::leanh::lean_box(0);
                        v_isShared_2687_ = v_isSharedCheck_2693_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2686_, 0, v_snd_2679_);
                    v___x_2689_ = v___x_2686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_snd_2679_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_cache_2681_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2692_,
                        2,
                        v_zetaDeltaFVarIds_2682_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 3, v_postponed_2683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 4, v_diag_2684_);
                    v___x_2689_ = v_reuseFailAlloc_2692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2690_ = lean_st_ref_set(v___y_2671_, v___x_2689_);
                v___x_2691_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2691_, 0, v_fst_2678_);
                return v___x_2691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg___boxed(
    mut v_e_2695_: *mut crate::leanh::LeanObject,
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(v_e_2695_, v___y_2696_);
    crate::leanh::lean_dec(v___y_2696_);
    return v_res_2698_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3(
    mut v_e_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
    mut v___y_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(v_e_2699_, v___y_2701_);
    return v___x_2705_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___boxed(
    mut v_e_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
    mut v___y_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2712_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3(v_e_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
    crate::leanh::lean_dec(v___y_2710_);
    crate::leanh::lean_dec_ref(v___y_2709_);
    crate::leanh::lean_dec(v___y_2708_);
    crate::leanh::lean_dec_ref(v___y_2707_);
    return v_res_2712_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(
    mut v_k_2713_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2714_: u8,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2728_: u8 = 0;
    let mut v_a_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2720_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_2714_,
                    v_k_2713_,
                    v___y_2715_,
                    v___y_2716_,
                    v___y_2717_,
                    v___y_2718_,
                );
                if crate::leanh::lean_obj_tag(v___x_2720_) == 0 {
                    v_a_2721_ = crate::leanh::lean_ctor_get(v___x_2720_, 0);
                    v_isSharedCheck_2728_ = (!crate::leanh::lean_is_exclusive(v___x_2720_)) as u8;
                    if v_isSharedCheck_2728_ == 0 {
                        v___x_2723_ = v___x_2720_;
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2721_);
                        crate::leanh::lean_dec(v___x_2720_);
                        v___x_2723_ = crate::leanh::lean_box(0);
                        v_isShared_2724_ = v_isSharedCheck_2728_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2729_ = crate::leanh::lean_ctor_get(v___x_2720_, 0);
                    v_isSharedCheck_2736_ = (!crate::leanh::lean_is_exclusive(v___x_2720_)) as u8;
                    if v_isSharedCheck_2736_ == 0 {
                        v___x_2731_ = v___x_2720_;
                        v_isShared_2732_ = v_isSharedCheck_2736_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2729_);
                        crate::leanh::lean_dec(v___x_2720_);
                        v___x_2731_ = crate::leanh::lean_box(0);
                        v_isShared_2732_ = v_isSharedCheck_2736_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2724_ == 0 {
                    v___x_2726_ = v___x_2723_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v_a_2721_);
                    v___x_2726_ = v_reuseFailAlloc_2727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2726_;
            }
            3 => {
                if v_isShared_2732_ == 0 {
                    v___x_2734_ = v___x_2731_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_a_2729_);
                    v___x_2734_ = v_reuseFailAlloc_2735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg___boxed(
    mut v_k_2737_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___y_2742_: *mut crate::leanh::LeanObject,
    mut v___y_2743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_2744_: u8 = 0;
    let mut v_res_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_2744_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_2738_) as u8);
    v_res_2745_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(v_k_2737_, v_allowLevelAssignments_boxed_2744_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
    crate::leanh::lean_dec(v___y_2742_);
    crate::leanh::lean_dec_ref(v___y_2741_);
    crate::leanh::lean_dec(v___y_2740_);
    crate::leanh::lean_dec_ref(v___y_2739_);
    return v_res_2745_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6(
    mut v_00_u03b1_2746_: *mut crate::leanh::LeanObject,
    mut v_k_2747_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2748_: u8,
    mut v___y_2749_: *mut crate::leanh::LeanObject,
    mut v___y_2750_: *mut crate::leanh::LeanObject,
    mut v___y_2751_: *mut crate::leanh::LeanObject,
    mut v___y_2752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(v_k_2747_, v_allowLevelAssignments_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
    return v___x_2754_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___boxed(
    mut v_00_u03b1_2755_: *mut crate::leanh::LeanObject,
    mut v_k_2756_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_2763_: u8 = 0;
    let mut v_res_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_2763_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_2757_) as u8);
    v_res_2764_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6(v_00_u03b1_2755_, v_k_2756_, v_allowLevelAssignments_boxed_2763_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
    crate::leanh::lean_dec(v___y_2761_);
    crate::leanh::lean_dec_ref(v___y_2760_);
    crate::leanh::lean_dec(v___y_2759_);
    crate::leanh::lean_dec_ref(v___y_2758_);
    return v_res_2764_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(
    mut v_keys_2765_: *mut crate::leanh::LeanObject,
    mut v_i_2766_: *mut crate::leanh::LeanObject,
    mut v_k_2767_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: u8 = 0;
    let mut v_k_x27_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2768_ = lean_array_get_size(v_keys_2765_);
                v___x_2769_ = lean_nat_dec_lt(v_i_2766_, v___x_2768_);
                if v___x_2769_ == 0 {
                    crate::leanh::lean_dec(v_i_2766_);
                    return v___x_2769_;
                } else {
                    v_k_x27_2770_ = lean_array_fget_borrowed(v_keys_2765_, v_i_2766_);
                    v___x_2771_ = l_Lean_instBEqMVarId_beq(v_k_2767_, v_k_x27_2770_);
                    if v___x_2771_ == 0 {
                        v___x_2772_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2773_ = lean_nat_add(v_i_2766_, v___x_2772_);
                        crate::leanh::lean_dec(v_i_2766_);
                        v_i_2766_ = v___x_2773_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2766_);
                        return v___x_2771_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(
    mut v_keys_2775_: *mut crate::leanh::LeanObject,
    mut v_i_2776_: *mut crate::leanh::LeanObject,
    mut v_k_2777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2778_: u8 = 0;
    let mut v_r_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2778_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(v_keys_2775_, v_i_2776_, v_k_2777_);
    crate::leanh::lean_dec(v_k_2777_);
    crate::leanh::lean_dec_ref(v_keys_2775_);
    v_r_2779_ = crate::leanh::lean_box((v_res_2778_) as usize);
    return v_r_2779_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_2780_: usize = 0;
    let mut v___x_2781_: usize = 0;
    let mut v___x_2782_: usize = 0;
    v___x_2780_ = 5usize;
    v___x_2781_ = 1usize;
    v___x_2782_ = lean_usize_shift_left(v___x_2781_, v___x_2780_);
    return v___x_2782_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_2783_: usize = 0;
    let mut v___x_2784_: usize = 0;
    let mut v___x_2785_: usize = 0;
    v___x_2783_ = 1usize;
    v___x_2784_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__0);
    v___x_2785_ = lean_usize_sub(v___x_2784_, v___x_2783_);
    return v___x_2785_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(
    mut v_x_2786_: *mut crate::leanh::LeanObject,
    mut v_x_2787_: usize,
    mut v_x_2788_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: usize = 0;
    let mut v___x_2792_: usize = 0;
    let mut v___x_2793_: usize = 0;
    let mut v_j_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: u8 = 0;
    let mut v_node_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: usize = 0;
    let mut v___x_2801_: u8 = 0;
    let mut v_ks_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2786_) == 0 {
                    v_es_2789_ = crate::leanh::lean_ctor_get(v_x_2786_, 0);
                    v___x_2790_ = crate::leanh::lean_box(2);
                    v___x_2791_ = 5usize;
                    v___x_2792_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___closed__1);
                    v___x_2793_ = lean_usize_land(v_x_2787_, v___x_2792_);
                    v_j_2794_ = lean_usize_to_nat(v___x_2793_);
                    v___x_2795_ = lean_array_get_borrowed(v___x_2790_, v_es_2789_, v_j_2794_);
                    crate::leanh::lean_dec(v_j_2794_);
                    match crate::leanh::lean_obj_tag(v___x_2795_) {
                        0 => {
                            v_key_2796_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                            v___x_2797_ = l_Lean_instBEqMVarId_beq(v_x_2788_, v_key_2796_);
                            return v___x_2797_;
                        }
                        1 => {
                            v_node_2798_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                            v___x_2799_ = lean_usize_shift_right(v_x_2787_, v___x_2791_);
                            v_x_2786_ = v_node_2798_;
                            v_x_2787_ = v___x_2799_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2801_ = 0;
                            return v___x_2801_;
                        }
                    }
                } else {
                    v_ks_2802_ = crate::leanh::lean_ctor_get(v_x_2786_, 0);
                    v___x_2803_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2804_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(v_ks_2802_, v___x_2803_, v_x_2788_);
                    return v___x_2804_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_x_2805_: *mut crate::leanh::LeanObject,
    mut v_x_2806_: *mut crate::leanh::LeanObject,
    mut v_x_2807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9322__boxed_2808_: usize = 0;
    let mut v_res_2809_: u8 = 0;
    let mut v_r_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9322__boxed_2808_ = crate::leanh::lean_unbox_usize(v_x_2806_);
    crate::leanh::lean_dec(v_x_2806_);
    v_res_2809_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(v_x_2805_, v_x_9322__boxed_2808_, v_x_2807_);
    crate::leanh::lean_dec(v_x_2807_);
    crate::leanh::lean_dec_ref(v_x_2805_);
    v_r_2810_ = crate::leanh::lean_box((v_res_2809_) as usize);
    return v_r_2810_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(
    mut v_x_2811_: *mut crate::leanh::LeanObject,
    mut v_x_2812_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2813_: u64 = 0;
    let mut v___x_2814_: usize = 0;
    let mut v___x_2815_: u8 = 0;
    v___x_2813_ = l_Lean_instHashableMVarId_hash(v_x_2812_);
    v___x_2814_ = lean_uint64_to_usize(v___x_2813_);
    v___x_2815_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(v_x_2811_, v___x_2814_, v_x_2812_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg___boxed(
    mut v_x_2816_: *mut crate::leanh::LeanObject,
    mut v_x_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2818_: u8 = 0;
    let mut v_r_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2818_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(v_x_2816_, v_x_2817_);
    crate::leanh::lean_dec(v_x_2817_);
    crate::leanh::lean_dec_ref(v_x_2816_);
    v_r_2819_ = crate::leanh::lean_box((v_res_2818_) as usize);
    return v_r_2819_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(
    mut v_mvarId_2820_: *mut crate::leanh::LeanObject,
    mut v___y_2821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: u8 = 0;
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2823_ = lean_st_ref_get(v___y_2821_);
    v_mctx_2824_ = crate::leanh::lean_ctor_get(v___x_2823_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2824_);
    crate::leanh::lean_dec(v___x_2823_);
    v_dAssignment_2825_ = crate::leanh::lean_ctor_get(v_mctx_2824_, 9);
    crate::leanh::lean_inc_ref(v_dAssignment_2825_);
    crate::leanh::lean_dec_ref(v_mctx_2824_);
    v___x_2826_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(v_dAssignment_2825_, v_mvarId_2820_);
    crate::leanh::lean_dec_ref(v_dAssignment_2825_);
    v___x_2827_ = crate::leanh::lean_box((v___x_2826_) as usize);
    v___x_2828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2828_, 0, v___x_2827_);
    return v___x_2828_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg___boxed(
    mut v_mvarId_2829_: *mut crate::leanh::LeanObject,
    mut v___y_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(v_mvarId_2829_, v___y_2830_);
    crate::leanh::lean_dec(v___y_2830_);
    crate::leanh::lean_dec(v_mvarId_2829_);
    return v_res_2832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(
    mut v_as_2833_: *mut crate::leanh::LeanObject,
    mut v_i_2834_: usize,
    mut v_stop_2835_: usize,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2848_: u8 = 0;
    let mut v___x_2849_: u8 = 0;
    let mut v___x_2850_: usize = 0;
    let mut v___x_2851_: usize = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2841_ = lean_usize_dec_eq(v_i_2834_, v_stop_2835_);
                if v___x_2841_ == 0 {
                    v___x_2842_ = lean_array_uget_borrowed(v_as_2833_, v_i_2834_);
                    v___x_2843_ = l_Lean_Expr_mvarId_x21(v___x_2842_);
                    v___x_2844_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(v___x_2843_, v___y_2837_);
                    crate::leanh::lean_dec(v___x_2843_);
                    if crate::leanh::lean_obj_tag(v___x_2844_) == 0 {
                        v_a_2845_ = crate::leanh::lean_ctor_get(v___x_2844_, 0);
                        v_isSharedCheck_2856_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2844_)) as u8;
                        if v_isSharedCheck_2856_ == 0 {
                            v___x_2847_ = v___x_2844_;
                            v_isShared_2848_ = v_isSharedCheck_2856_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2845_);
                            crate::leanh::lean_dec(v___x_2844_);
                            v___x_2847_ = crate::leanh::lean_box(0);
                            v_isShared_2848_ = v_isSharedCheck_2856_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_2844_;
                    }
                } else {
                    v___x_2857_ = 0;
                    v___x_2858_ = crate::leanh::lean_box((v___x_2857_) as usize);
                    v___x_2859_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2859_, 0, v___x_2858_);
                    return v___x_2859_;
                }
            }
            1 => {
                v___x_2849_ = (crate::leanh::lean_unbox(v_a_2845_) as u8);
                if v___x_2849_ == 0 {
                    crate::leanh::lean_del_object(v___x_2847_);
                    crate::leanh::lean_dec(v_a_2845_);
                    v___x_2850_ = 1usize;
                    v___x_2851_ = lean_usize_add(v_i_2834_, v___x_2850_);
                    v_i_2834_ = v___x_2851_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_2848_ == 0 {
                        v___x_2854_ = v___x_2847_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2855_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2845_);
                        v___x_2854_ = v_reuseFailAlloc_2855_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5___boxed(
    mut v_as_2860_: *mut crate::leanh::LeanObject,
    mut v_i_2861_: *mut crate::leanh::LeanObject,
    mut v_stop_2862_: *mut crate::leanh::LeanObject,
    mut v___y_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2868_: usize = 0;
    let mut v_stop_boxed_2869_: usize = 0;
    let mut v_res_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2868_ = crate::leanh::lean_unbox_usize(v_i_2861_);
    crate::leanh::lean_dec(v_i_2861_);
    v_stop_boxed_2869_ = crate::leanh::lean_unbox_usize(v_stop_2862_);
    crate::leanh::lean_dec(v_stop_2862_);
    v_res_2870_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(v_as_2860_, v_i_boxed_2868_, v_stop_boxed_2869_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
    crate::leanh::lean_dec(v___y_2866_);
    crate::leanh::lean_dec_ref(v___y_2865_);
    crate::leanh::lean_dec(v___y_2864_);
    crate::leanh::lean_dec_ref(v___y_2863_);
    crate::leanh::lean_dec_ref(v_as_2860_);
    return v_res_2870_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(
    mut v_mvarId_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2874_ = lean_st_ref_get(v___y_2872_);
    v_mctx_2875_ = crate::leanh::lean_ctor_get(v___x_2874_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2875_);
    crate::leanh::lean_dec(v___x_2874_);
    v_eAssignment_2876_ = crate::leanh::lean_ctor_get(v_mctx_2875_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_2876_);
    crate::leanh::lean_dec_ref(v_mctx_2875_);
    v___x_2877_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(v_eAssignment_2876_, v_mvarId_2871_);
    crate::leanh::lean_dec_ref(v_eAssignment_2876_);
    v___x_2878_ = crate::leanh::lean_box((v___x_2877_) as usize);
    v___x_2879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2878_);
    return v___x_2879_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg___boxed(
    mut v_mvarId_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2883_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(v_mvarId_2880_, v___y_2881_);
    crate::leanh::lean_dec(v___y_2881_);
    crate::leanh::lean_dec(v_mvarId_2880_);
    return v_res_2883_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(
    mut v_as_2884_: *mut crate::leanh::LeanObject,
    mut v_i_2885_: usize,
    mut v_stop_2886_: usize,
    mut v_b_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: usize = 0;
    let mut v___x_2896_: usize = 0;
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: u8 = 0;
    let mut v_a_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: u8 = 0;
    let mut v_a_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2915_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2898_ = lean_usize_dec_eq(v_i_2885_, v_stop_2886_);
                if v___x_2898_ == 0 {
                    v___x_2899_ = lean_array_uget_borrowed(v_as_2884_, v_i_2885_);
                    v___x_2902_ = l_Lean_Expr_mvarId_x21(v___x_2899_);
                    v___x_2903_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(v___x_2902_, v___y_2889_);
                    crate::leanh::lean_dec(v___x_2902_);
                    if crate::leanh::lean_obj_tag(v___x_2903_) == 0 {
                        v_a_2904_ = crate::leanh::lean_ctor_get(v___x_2903_, 0);
                        crate::leanh::lean_inc(v_a_2904_);
                        crate::leanh::lean_dec_ref_known(v___x_2903_, 1);
                        v___x_2905_ = (crate::leanh::lean_unbox(v_a_2904_) as u8);
                        crate::leanh::lean_dec(v_a_2904_);
                        if v___x_2905_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_2894_ = v_b_2887_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_2903_) == 0 {
                            v_a_2906_ = crate::leanh::lean_ctor_get(v___x_2903_, 0);
                            crate::leanh::lean_inc(v_a_2906_);
                            crate::leanh::lean_dec_ref_known(v___x_2903_, 1);
                            v___x_2907_ = (crate::leanh::lean_unbox(v_a_2906_) as u8);
                            crate::leanh::lean_dec(v_a_2906_);
                            if v___x_2907_ == 0 {
                                v_a_2894_ = v_b_2887_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2887_);
                            v_a_2908_ = crate::leanh::lean_ctor_get(v___x_2903_, 0);
                            v_isSharedCheck_2915_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2903_)) as u8;
                            if v_isSharedCheck_2915_ == 0 {
                                v___x_2910_ = v___x_2903_;
                                v_isShared_2911_ = v_isSharedCheck_2915_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2908_);
                                crate::leanh::lean_dec(v___x_2903_);
                                v___x_2910_ = crate::leanh::lean_box(0);
                                v_isShared_2911_ = v_isSharedCheck_2915_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_2916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2916_, 0, v_b_2887_);
                    return v___x_2916_;
                }
            }
            1 => {
                v___x_2895_ = 1usize;
                v___x_2896_ = lean_usize_add(v_i_2885_, v___x_2895_);
                v_i_2885_ = v___x_2896_;
                v_b_2887_ = v_a_2894_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v___x_2899_);
                v___x_2901_ = lean_array_push(v_b_2887_, v___x_2899_);
                v_a_2894_ = v___x_2901_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_2911_ == 0 {
                    v___x_2913_ = v___x_2910_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2914_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
                    v___x_2913_ = v_reuseFailAlloc_2914_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4___boxed(
    mut v_as_2917_: *mut crate::leanh::LeanObject,
    mut v_i_2918_: *mut crate::leanh::LeanObject,
    mut v_stop_2919_: *mut crate::leanh::LeanObject,
    mut v_b_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
    mut v___y_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2926_: usize = 0;
    let mut v_stop_boxed_2927_: usize = 0;
    let mut v_res_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2926_ = crate::leanh::lean_unbox_usize(v_i_2918_);
    crate::leanh::lean_dec(v_i_2918_);
    v_stop_boxed_2927_ = crate::leanh::lean_unbox_usize(v_stop_2919_);
    crate::leanh::lean_dec(v_stop_2919_);
    v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(v_as_2917_, v_i_boxed_2926_, v_stop_boxed_2927_, v_b_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
    crate::leanh::lean_dec(v___y_2924_);
    crate::leanh::lean_dec_ref(v___y_2923_);
    crate::leanh::lean_dec(v___y_2922_);
    crate::leanh::lean_dec_ref(v___y_2921_);
    crate::leanh::lean_dec_ref(v_as_2917_);
    return v_res_2928_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(
    mut v_as_2934_: *mut crate::leanh::LeanObject,
    mut v_sz_2935_: usize,
    mut v_i_2936_: usize,
    mut v_b_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
    mut v___y_2941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: usize = 0;
    let mut v___x_2946_: usize = 0;
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2958_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u8 = 0;
    let mut v_arg_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: u8 = 0;
    let mut v_arg_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u8 = 0;
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_a_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_a_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3006_: u8 = 0;
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3010_: u8 = 0;
    let mut v_a_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3014_: u8 = 0;
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3018_: u8 = 0;
    let mut v_isSharedCheck_3019_: u8 = 0;
    let mut v_unused_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut v_a_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3032_: u8 = 0;
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2948_ = lean_usize_dec_lt(v_i_2936_, v_sz_2935_);
                if v___x_2948_ == 0 {
                    v___x_2949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2949_, 0, v_b_2937_);
                    return v___x_2949_;
                } else {
                    v_a_2950_ = lean_array_uget_borrowed(v_as_2934_, v_i_2936_);
                    crate::leanh::lean_inc(v___y_2941_);
                    crate::leanh::lean_inc_ref(v___y_2940_);
                    crate::leanh::lean_inc(v___y_2939_);
                    crate::leanh::lean_inc_ref(v___y_2938_);
                    crate::leanh::lean_inc(v_a_2950_);
                    v___x_2951_ = lean_infer_type(
                        v_a_2950_,
                        v___y_2938_,
                        v___y_2939_,
                        v___y_2940_,
                        v___y_2941_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2951_) == 0 {
                        v_a_2952_ = crate::leanh::lean_ctor_get(v___x_2951_, 0);
                        crate::leanh::lean_inc(v_a_2952_);
                        crate::leanh::lean_dec_ref_known(v___x_2951_, 1);
                        v___x_2953_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_2952_, v___y_2939_);
                        if crate::leanh::lean_obj_tag(v___x_2953_) == 0 {
                            v_a_2954_ = crate::leanh::lean_ctor_get(v___x_2953_, 0);
                            crate::leanh::lean_inc(v_a_2954_);
                            crate::leanh::lean_dec_ref_known(v___x_2953_, 1);
                            v_snd_2955_ = crate::leanh::lean_ctor_get(v_b_2937_, 1);
                            v_isSharedCheck_3019_ =
                                (!crate::leanh::lean_is_exclusive(v_b_2937_)) as u8;
                            if v_isSharedCheck_3019_ == 0 {
                                v_unused_3020_ = crate::leanh::lean_ctor_get(v_b_2937_, 0);
                                crate::leanh::lean_dec(v_unused_3020_);
                                v___x_2957_ = v_b_2937_;
                                v_isShared_2958_ = v_isSharedCheck_3019_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_2955_);
                                crate::leanh::lean_dec(v_b_2937_);
                                v___x_2957_ = crate::leanh::lean_box(0);
                                v_isShared_2958_ = v_isSharedCheck_3019_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2937_);
                            v_a_3021_ = crate::leanh::lean_ctor_get(v___x_2953_, 0);
                            v_isSharedCheck_3028_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2953_)) as u8;
                            if v_isSharedCheck_3028_ == 0 {
                                v___x_3023_ = v___x_2953_;
                                v_isShared_3024_ = v_isSharedCheck_3028_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3021_);
                                crate::leanh::lean_dec(v___x_2953_);
                                v___x_3023_ = crate::leanh::lean_box(0);
                                v_isShared_3024_ = v_isSharedCheck_3028_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2937_);
                        v_a_3029_ = crate::leanh::lean_ctor_get(v___x_2951_, 0);
                        v_isSharedCheck_3036_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2951_)) as u8;
                        if v_isSharedCheck_3036_ == 0 {
                            v___x_3031_ = v___x_2951_;
                            v_isShared_3032_ = v_isSharedCheck_3036_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3029_);
                            crate::leanh::lean_dec(v___x_2951_);
                            v___x_3031_ = crate::leanh::lean_box(0);
                            v_isShared_3032_ = v_isSharedCheck_3036_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2945_ = 1usize;
                v___x_2946_ = lean_usize_add(v_i_2936_, v___x_2945_);
                v_i_2936_ = v___x_2946_;
                v_b_2937_ = v_a_2944_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2959_ = crate::leanh::lean_box(0);
                v___x_2964_ = l_Lean_Expr_cleanupAnnotations(v_a_2954_);
                v___x_2965_ = l_Lean_Expr_isApp(v___x_2964_);
                if v___x_2965_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2964_);
                    state = 3;
                    continue;
                } else {
                    v_arg_2966_ = crate::leanh::lean_ctor_get(v___x_2964_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2966_);
                    v___x_2967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2964_);
                    v___x_2968_ = l_Lean_Expr_isApp(v___x_2967_);
                    if v___x_2968_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2967_);
                        crate::leanh::lean_dec_ref(v_arg_2966_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_2969_ = crate::leanh::lean_ctor_get(v___x_2967_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2969_);
                        v___x_2970_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2967_);
                        v___x_2971_ = l_Lean_Expr_isApp(v___x_2970_);
                        if v___x_2971_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2970_);
                            crate::leanh::lean_dec_ref(v_arg_2969_);
                            crate::leanh::lean_dec_ref(v_arg_2966_);
                            state = 3;
                            continue;
                        } else {
                            v___x_2972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2970_);
                            v___x_2973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__1;
                            v___x_2974_ = l_Lean_Expr_isConstOf(v___x_2972_, v___x_2973_);
                            crate::leanh::lean_dec_ref(v___x_2972_);
                            if v___x_2974_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2969_);
                                crate::leanh::lean_dec_ref(v_arg_2966_);
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_2957_);
                                crate::leanh::lean_inc_ref(v_arg_2969_);
                                v___x_2975_ = l_Lean_Meta_isExprDefEq(
                                    v_arg_2969_,
                                    v_arg_2966_,
                                    v___y_2938_,
                                    v___y_2939_,
                                    v___y_2940_,
                                    v___y_2941_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2975_) == 0 {
                                    v_a_2976_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                    crate::leanh::lean_inc(v_a_2976_);
                                    crate::leanh::lean_dec_ref_known(v___x_2975_, 1);
                                    v___x_2977_ = (crate::leanh::lean_unbox(v_a_2976_) as u8);
                                    crate::leanh::lean_dec(v_a_2976_);
                                    if v___x_2977_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_2969_);
                                        v___x_2978_ =
                                            crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2978_, 0, v___x_2959_);
                                        crate::leanh::lean_ctor_set(v___x_2978_, 1, v_snd_2955_);
                                        v_a_2944_ = v___x_2978_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_2979_ = l_Lean_Meta_mkEqRefl(
                                            v_arg_2969_,
                                            v___y_2938_,
                                            v___y_2939_,
                                            v___y_2940_,
                                            v___y_2941_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2979_) == 0 {
                                            v_a_2980_ = crate::leanh::lean_ctor_get(v___x_2979_, 0);
                                            crate::leanh::lean_inc(v_a_2980_);
                                            crate::leanh::lean_dec_ref_known(v___x_2979_, 1);
                                            v___x_2981_ = l_Lean_Expr_mvarId_x21(v_a_2950_);
                                            crate::leanh::lean_inc(v___y_2941_);
                                            crate::leanh::lean_inc_ref(v___y_2940_);
                                            crate::leanh::lean_inc(v___y_2939_);
                                            crate::leanh::lean_inc_ref(v___y_2938_);
                                            v___x_2982_ = lean_checked_assign(
                                                v___x_2981_,
                                                v_a_2980_,
                                                v___y_2938_,
                                                v___y_2939_,
                                                v___y_2940_,
                                                v___y_2941_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2982_) == 0 {
                                                v_a_2983_ =
                                                    crate::leanh::lean_ctor_get(v___x_2982_, 0);
                                                v_isSharedCheck_2994_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2982_))
                                                        as u8;
                                                if v_isSharedCheck_2994_ == 0 {
                                                    v___x_2985_ = v___x_2982_;
                                                    v_isShared_2986_ = v_isSharedCheck_2994_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2983_);
                                                    crate::leanh::lean_dec(v___x_2982_);
                                                    v___x_2985_ = crate::leanh::lean_box(0);
                                                    v_isShared_2986_ = v_isSharedCheck_2994_;
                                                    state = 5;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_snd_2955_);
                                                v_a_2995_ =
                                                    crate::leanh::lean_ctor_get(v___x_2982_, 0);
                                                v_isSharedCheck_3002_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2982_))
                                                        as u8;
                                                if v_isSharedCheck_3002_ == 0 {
                                                    v___x_2997_ = v___x_2982_;
                                                    v_isShared_2998_ = v_isSharedCheck_3002_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2995_);
                                                    crate::leanh::lean_dec(v___x_2982_);
                                                    v___x_2997_ = crate::leanh::lean_box(0);
                                                    v_isShared_2998_ = v_isSharedCheck_3002_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_snd_2955_);
                                            v_a_3003_ = crate::leanh::lean_ctor_get(v___x_2979_, 0);
                                            v_isSharedCheck_3010_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2979_))
                                                    as u8;
                                            if v_isSharedCheck_3010_ == 0 {
                                                v___x_3005_ = v___x_2979_;
                                                v_isShared_3006_ = v_isSharedCheck_3010_;
                                                state = 9;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3003_);
                                                crate::leanh::lean_dec(v___x_2979_);
                                                v___x_3005_ = crate::leanh::lean_box(0);
                                                v_isShared_3006_ = v_isSharedCheck_3010_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_2969_);
                                    crate::leanh::lean_dec(v_snd_2955_);
                                    v_a_3011_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                                    v_isSharedCheck_3018_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2975_)) as u8;
                                    if v_isSharedCheck_3018_ == 0 {
                                        v___x_3013_ = v___x_2975_;
                                        v_isShared_3014_ = v_isSharedCheck_3018_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3011_);
                                        crate::leanh::lean_dec(v___x_2975_);
                                        v___x_3013_ = crate::leanh::lean_box(0);
                                        v_isShared_3014_ = v_isSharedCheck_3018_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_2958_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2957_, 0, v___x_2959_);
                    v___x_2962_ = v___x_2957_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_snd_2955_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_2944_ = v___x_2962_;
                state = 1;
                continue;
            }
            5 => {
                v___x_2987_ = (crate::leanh::lean_unbox(v_a_2983_) as u8);
                if v___x_2987_ == 0 {
                    crate::leanh::lean_dec(v_a_2983_);
                    v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___closed__2;
                    v___x_2989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2989_, 0, v___x_2988_);
                    crate::leanh::lean_ctor_set(v___x_2989_, 1, v_snd_2955_);
                    if v_isShared_2986_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2985_, 0, v___x_2989_);
                        v___x_2991_ = v___x_2985_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
                        v___x_2991_ = v_reuseFailAlloc_2992_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2985_);
                    crate::leanh::lean_dec(v_snd_2955_);
                    v___x_2993_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2993_, 0, v___x_2959_);
                    crate::leanh::lean_ctor_set(v___x_2993_, 1, v_a_2983_);
                    v_a_2944_ = v___x_2993_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                return v___x_2991_;
            }
            7 => {
                if v_isShared_2998_ == 0 {
                    v___x_3000_ = v___x_2997_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
                    v___x_3000_ = v_reuseFailAlloc_3001_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3000_;
            }
            9 => {
                if v_isShared_3006_ == 0 {
                    v___x_3008_ = v___x_3005_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
                    v___x_3008_ = v_reuseFailAlloc_3009_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3008_;
            }
            11 => {
                if v_isShared_3014_ == 0 {
                    v___x_3016_ = v___x_3013_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
                    v___x_3016_ = v_reuseFailAlloc_3017_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3016_;
            }
            13 => {
                if v_isShared_3024_ == 0 {
                    v___x_3026_ = v___x_3023_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
                    v___x_3026_ = v_reuseFailAlloc_3027_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3026_;
            }
            15 => {
                if v_isShared_3032_ == 0 {
                    v___x_3034_ = v___x_3031_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
                    v___x_3034_ = v_reuseFailAlloc_3035_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1___boxed(
    mut v_as_3037_: *mut crate::leanh::LeanObject,
    mut v_sz_3038_: *mut crate::leanh::LeanObject,
    mut v_i_3039_: *mut crate::leanh::LeanObject,
    mut v_b_3040_: *mut crate::leanh::LeanObject,
    mut v___y_3041_: *mut crate::leanh::LeanObject,
    mut v___y_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3046_: usize = 0;
    let mut v_i_boxed_3047_: usize = 0;
    let mut v_res_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3046_ = crate::leanh::lean_unbox_usize(v_sz_3038_);
    crate::leanh::lean_dec(v_sz_3038_);
    v_i_boxed_3047_ = crate::leanh::lean_unbox_usize(v_i_3039_);
    crate::leanh::lean_dec(v_i_3039_);
    v_res_3048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(v_as_3037_, v_sz_boxed_3046_, v_i_boxed_3047_, v_b_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_);
    crate::leanh::lean_dec(v___y_3044_);
    crate::leanh::lean_dec_ref(v___y_3043_);
    crate::leanh::lean_dec(v___y_3042_);
    crate::leanh::lean_dec_ref(v___y_3041_);
    crate::leanh::lean_dec_ref(v_as_3037_);
    return v_res_3048_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0(
    mut v_prop_3049_: *mut crate::leanh::LeanObject,
    mut v_proof_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
    mut v___y_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v_fst_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3065_: u8 = 0;
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3073_: usize = 0;
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v_fst_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: u8 = 0;
    let mut v___y_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3098_: u8 = 0;
    let mut v_val_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3103_: u8 = 0;
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut v_a_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut v_a_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v_a_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3146_: u8 = 0;
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v___y_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut v_a_3165_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: u8 = 0;
    let mut v___x_3173_: u8 = 0;
    let mut v___x_3174_: usize = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: usize = 0;
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: usize = 0;
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: u8 = 0;
    let mut v_a_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3193_: u8 = 0;
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut v_unused_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v_reuseFailAlloc_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v_a_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3219_: u8 = 0;
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3056_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_forallMetaTelescopeReducingAndUnfoldingNot(v_prop_3049_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
                if crate::leanh::lean_obj_tag(v___x_3056_) == 0 {
                    v_a_3057_ = crate::leanh::lean_ctor_get(v___x_3056_, 0);
                    v_isSharedCheck_3215_ = (!crate::leanh::lean_is_exclusive(v___x_3056_)) as u8;
                    if v_isSharedCheck_3215_ == 0 {
                        v___x_3059_ = v___x_3056_;
                        v_isShared_3060_ = v_isSharedCheck_3215_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3057_);
                        crate::leanh::lean_dec(v___x_3056_);
                        v___x_3059_ = crate::leanh::lean_box(0);
                        v_isShared_3060_ = v_isSharedCheck_3215_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_proof_3050_);
                    v_a_3216_ = crate::leanh::lean_ctor_get(v___x_3056_, 0);
                    v_isSharedCheck_3223_ = (!crate::leanh::lean_is_exclusive(v___x_3056_)) as u8;
                    if v_isSharedCheck_3223_ == 0 {
                        v___x_3218_ = v___x_3056_;
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3216_);
                        crate::leanh::lean_dec(v___x_3056_);
                        v___x_3218_ = crate::leanh::lean_box(0);
                        v_isShared_3219_ = v_isSharedCheck_3223_;
                        state = 32;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3061_ = crate::leanh::lean_ctor_get(v_a_3057_, 0);
                v_snd_3062_ = crate::leanh::lean_ctor_get(v_a_3057_, 1);
                v_isSharedCheck_3214_ = (!crate::leanh::lean_is_exclusive(v_a_3057_)) as u8;
                if v_isSharedCheck_3214_ == 0 {
                    v___x_3064_ = v_a_3057_;
                    v_isShared_3065_ = v_isSharedCheck_3214_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3062_);
                    crate::leanh::lean_inc(v_fst_3061_);
                    crate::leanh::lean_dec(v_a_3057_);
                    v___x_3064_ = crate::leanh::lean_box(0);
                    v_isShared_3065_ = v_isSharedCheck_3214_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3066_ = lean_array_get_size(v_fst_3061_);
                v___x_3067_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3068_ = lean_nat_dec_eq(v___x_3066_, v___x_3067_);
                if v___x_3068_ == 0 {
                    crate::leanh::lean_del_object(v___x_3059_);
                    v___x_3069_ = crate::leanh::lean_box(0);
                    v___x_3070_ = crate::leanh::lean_box((v___x_3068_) as usize);
                    if v_isShared_3065_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3064_, 1, v___x_3070_);
                        crate::leanh::lean_ctor_set(v___x_3064_, 0, v___x_3069_);
                        v___x_3072_ = v___x_3064_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 0, v___x_3069_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3209_, 1, v___x_3070_);
                        v___x_3072_ = v_reuseFailAlloc_3209_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3064_);
                    crate::leanh::lean_dec(v_snd_3062_);
                    crate::leanh::lean_dec(v_fst_3061_);
                    crate::leanh::lean_dec_ref(v_proof_3050_);
                    v___x_3210_ = crate::leanh::lean_box(0);
                    if v_isShared_3060_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3059_, 0, v___x_3210_);
                        v___x_3212_ = v___x_3059_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3213_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 0, v___x_3210_);
                        v___x_3212_ = v_reuseFailAlloc_3213_;
                        state = 31;
                        continue;
                    }
                }
            }
            3 => {
                v_sz_3073_ = lean_array_size(v_fst_3061_);
                v___x_3074_ = 0usize;
                v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__1(v_fst_3061_, v_sz_3073_, v___x_3074_, v___x_3072_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
                if crate::leanh::lean_obj_tag(v___x_3075_) == 0 {
                    v_a_3076_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                    v_isSharedCheck_3200_ = (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                    if v_isSharedCheck_3200_ == 0 {
                        v___x_3078_ = v___x_3075_;
                        v_isShared_3079_ = v_isSharedCheck_3200_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3076_);
                        crate::leanh::lean_dec(v___x_3075_);
                        v___x_3078_ = crate::leanh::lean_box(0);
                        v_isShared_3079_ = v_isSharedCheck_3200_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_3062_);
                    crate::leanh::lean_dec(v_fst_3061_);
                    crate::leanh::lean_dec_ref(v_proof_3050_);
                    v_a_3201_ = crate::leanh::lean_ctor_get(v___x_3075_, 0);
                    v_isSharedCheck_3208_ = (!crate::leanh::lean_is_exclusive(v___x_3075_)) as u8;
                    if v_isSharedCheck_3208_ == 0 {
                        v___x_3203_ = v___x_3075_;
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3201_);
                        crate::leanh::lean_dec(v___x_3075_);
                        v___x_3203_ = crate::leanh::lean_box(0);
                        v_isShared_3204_ = v_isSharedCheck_3208_;
                        state = 29;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_3080_ = crate::leanh::lean_ctor_get(v_a_3076_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3080_) == 0 {
                    v_snd_3081_ = crate::leanh::lean_ctor_get(v_a_3076_, 1);
                    v_isSharedCheck_3194_ = (!crate::leanh::lean_is_exclusive(v_a_3076_)) as u8;
                    if v_isSharedCheck_3194_ == 0 {
                        v_unused_3195_ = crate::leanh::lean_ctor_get(v_a_3076_, 0);
                        crate::leanh::lean_dec(v_unused_3195_);
                        v___x_3083_ = v_a_3076_;
                        v_isShared_3084_ = v_isSharedCheck_3194_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3081_);
                        crate::leanh::lean_dec(v_a_3076_);
                        v___x_3083_ = crate::leanh::lean_box(0);
                        v_isShared_3084_ = v_isSharedCheck_3194_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3080_);
                    crate::leanh::lean_dec(v_a_3076_);
                    crate::leanh::lean_dec(v_snd_3062_);
                    crate::leanh::lean_dec(v_fst_3061_);
                    crate::leanh::lean_dec_ref(v_proof_3050_);
                    v_val_3196_ = crate::leanh::lean_ctor_get(v_fst_3080_, 0);
                    crate::leanh::lean_inc(v_val_3196_);
                    crate::leanh::lean_dec_ref_known(v_fst_3080_, 1);
                    if v_isShared_3079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3078_, 0, v_val_3196_);
                        v___x_3198_ = v___x_3078_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_3199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_val_3196_);
                        v___x_3198_ = v_reuseFailAlloc_3199_;
                        state = 28;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3085_ = (crate::leanh::lean_unbox(v_snd_3081_) as u8);
                crate::leanh::lean_dec(v_snd_3081_);
                if v___x_3085_ == 0 {
                    crate::leanh::lean_del_object(v___x_3083_);
                    crate::leanh::lean_dec(v_snd_3062_);
                    crate::leanh::lean_dec(v_fst_3061_);
                    crate::leanh::lean_dec_ref(v_proof_3050_);
                    if v_isShared_3079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3078_, 0, v___x_3069_);
                        v___x_3087_ = v___x_3078_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3069_);
                        v___x_3087_ = v_reuseFailAlloc_3088_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_3089_ = 1;
                    v___x_3181_ = lean_nat_dec_lt(v___x_3067_, v___x_3066_);
                    if v___x_3181_ == 0 {
                        v_a_3165_ = v___x_3068_;
                        state = 24;
                        continue;
                    } else {
                        if v___x_3181_ == 0 {
                            v_a_3165_ = v___x_3068_;
                            state = 24;
                            continue;
                        } else {
                            v___x_3182_ = lean_usize_of_nat(v___x_3066_);
                            v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__5(v_fst_3061_, v___x_3074_, v___x_3182_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
                            if crate::leanh::lean_obj_tag(v___x_3183_) == 0 {
                                v_a_3184_ = crate::leanh::lean_ctor_get(v___x_3183_, 0);
                                crate::leanh::lean_inc(v_a_3184_);
                                crate::leanh::lean_dec_ref_known(v___x_3183_, 1);
                                v___x_3185_ = (crate::leanh::lean_unbox(v_a_3184_) as u8);
                                crate::leanh::lean_dec(v_a_3184_);
                                v_a_3165_ = v___x_3185_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_3083_);
                                crate::leanh::lean_del_object(v___x_3078_);
                                crate::leanh::lean_dec(v_snd_3062_);
                                crate::leanh::lean_dec(v_fst_3061_);
                                crate::leanh::lean_dec_ref(v_proof_3050_);
                                v_a_3186_ = crate::leanh::lean_ctor_get(v___x_3183_, 0);
                                v_isSharedCheck_3193_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3183_)) as u8;
                                if v_isSharedCheck_3193_ == 0 {
                                    v___x_3188_ = v___x_3183_;
                                    v_isShared_3189_ = v_isSharedCheck_3193_;
                                    state = 26;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3186_);
                                    crate::leanh::lean_dec(v___x_3183_);
                                    v___x_3188_ = crate::leanh::lean_box(0);
                                    v_isShared_3189_ = v_isSharedCheck_3193_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                return v___x_3087_;
            }
            7 => {
                v___x_3094_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f(v_a_3093_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
                if crate::leanh::lean_obj_tag(v___x_3094_) == 0 {
                    v_a_3095_ = crate::leanh::lean_ctor_get(v___x_3094_, 0);
                    v_isSharedCheck_3142_ = (!crate::leanh::lean_is_exclusive(v___x_3094_)) as u8;
                    if v_isSharedCheck_3142_ == 0 {
                        v___x_3097_ = v___x_3094_;
                        v_isShared_3098_ = v_isSharedCheck_3142_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3095_);
                        crate::leanh::lean_dec(v___x_3094_);
                        v___x_3097_ = crate::leanh::lean_box(0);
                        v_isShared_3098_ = v_isSharedCheck_3142_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3092_);
                    crate::leanh::lean_dec_ref(v___y_3091_);
                    crate::leanh::lean_del_object(v___x_3083_);
                    v_a_3143_ = crate::leanh::lean_ctor_get(v___x_3094_, 0);
                    v_isSharedCheck_3150_ = (!crate::leanh::lean_is_exclusive(v___x_3094_)) as u8;
                    if v_isSharedCheck_3150_ == 0 {
                        v___x_3145_ = v___x_3094_;
                        v_isShared_3146_ = v_isSharedCheck_3150_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3143_);
                        crate::leanh::lean_dec(v___x_3094_);
                        v___x_3145_ = crate::leanh::lean_box(0);
                        v_isShared_3146_ = v_isSharedCheck_3150_;
                        state = 19;
                        continue;
                    }
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_3095_) == 1 {
                    crate::leanh::lean_del_object(v___x_3097_);
                    v_val_3099_ = crate::leanh::lean_ctor_get(v_a_3095_, 0);
                    v_isSharedCheck_3138_ = (!crate::leanh::lean_is_exclusive(v_a_3095_)) as u8;
                    if v_isSharedCheck_3138_ == 0 {
                        v___x_3101_ = v_a_3095_;
                        v_isShared_3102_ = v_isSharedCheck_3138_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3099_);
                        crate::leanh::lean_dec(v_a_3095_);
                        v___x_3101_ = crate::leanh::lean_box(0);
                        v_isShared_3102_ = v_isSharedCheck_3138_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3095_);
                    crate::leanh::lean_dec_ref(v___y_3092_);
                    crate::leanh::lean_dec_ref(v___y_3091_);
                    crate::leanh::lean_del_object(v___x_3083_);
                    if v_isShared_3098_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3097_, 0, v___x_3069_);
                        v___x_3140_ = v___x_3097_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3069_);
                        v___x_3140_ = v_reuseFailAlloc_3141_;
                        state = 18;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3103_ = 0;
                v___x_3104_ = l_Lean_Meta_mkForallFVars(
                    v_val_3099_,
                    v___y_3091_,
                    v___x_3068_,
                    v___x_3089_,
                    v___x_3089_,
                    v___x_3103_,
                    v___y_3051_,
                    v___y_3052_,
                    v___y_3053_,
                    v___y_3054_,
                );
                if crate::leanh::lean_obj_tag(v___x_3104_) == 0 {
                    v_a_3105_ = crate::leanh::lean_ctor_get(v___x_3104_, 0);
                    crate::leanh::lean_inc(v_a_3105_);
                    crate::leanh::lean_dec_ref_known(v___x_3104_, 1);
                    v___x_3106_ = 1;
                    v___x_3107_ = l_Lean_Meta_mkLambdaFVars(
                        v_val_3099_,
                        v___y_3092_,
                        v___x_3068_,
                        v___x_3089_,
                        v___x_3068_,
                        v___x_3089_,
                        v___x_3106_,
                        v___y_3051_,
                        v___y_3052_,
                        v___y_3053_,
                        v___y_3054_,
                    );
                    crate::leanh::lean_dec(v_val_3099_);
                    if crate::leanh::lean_obj_tag(v___x_3107_) == 0 {
                        v_a_3108_ = crate::leanh::lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3121_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3121_ == 0 {
                            v___x_3110_ = v___x_3107_;
                            v_isShared_3111_ = v_isSharedCheck_3121_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3108_);
                            crate::leanh::lean_dec(v___x_3107_);
                            v___x_3110_ = crate::leanh::lean_box(0);
                            v_isShared_3111_ = v_isSharedCheck_3121_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3105_);
                        crate::leanh::lean_del_object(v___x_3101_);
                        crate::leanh::lean_del_object(v___x_3083_);
                        v_a_3122_ = crate::leanh::lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3129_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3129_ == 0 {
                            v___x_3124_ = v___x_3107_;
                            v_isShared_3125_ = v_isSharedCheck_3129_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3122_);
                            crate::leanh::lean_dec(v___x_3107_);
                            v___x_3124_ = crate::leanh::lean_box(0);
                            v_isShared_3125_ = v_isSharedCheck_3129_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3101_);
                    crate::leanh::lean_dec(v_val_3099_);
                    crate::leanh::lean_dec_ref(v___y_3092_);
                    crate::leanh::lean_del_object(v___x_3083_);
                    v_a_3130_ = crate::leanh::lean_ctor_get(v___x_3104_, 0);
                    v_isSharedCheck_3137_ = (!crate::leanh::lean_is_exclusive(v___x_3104_)) as u8;
                    if v_isSharedCheck_3137_ == 0 {
                        v___x_3132_ = v___x_3104_;
                        v_isShared_3133_ = v_isSharedCheck_3137_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3130_);
                        crate::leanh::lean_dec(v___x_3104_);
                        v___x_3132_ = crate::leanh::lean_box(0);
                        v_isShared_3133_ = v_isSharedCheck_3137_;
                        state = 16;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_3084_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3083_, 1, v_a_3108_);
                    crate::leanh::lean_ctor_set(v___x_3083_, 0, v_a_3105_);
                    v___x_3113_ = v___x_3083_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3120_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_a_3108_);
                    v___x_3113_ = v_reuseFailAlloc_3120_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3101_, 0, v___x_3113_);
                    v___x_3115_ = v___x_3101_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3113_);
                    v___x_3115_ = v_reuseFailAlloc_3119_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3115_);
                    v___x_3117_ = v___x_3110_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
                    v___x_3117_ = v_reuseFailAlloc_3118_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3117_;
            }
            14 => {
                if v_isShared_3125_ == 0 {
                    v___x_3127_ = v___x_3124_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3128_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
                    v___x_3127_ = v_reuseFailAlloc_3128_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3127_;
            }
            16 => {
                if v_isShared_3133_ == 0 {
                    v___x_3135_ = v___x_3132_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
                    v___x_3135_ = v_reuseFailAlloc_3136_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3135_;
            }
            18 => {
                return v___x_3140_;
            }
            19 => {
                if v_isShared_3146_ == 0 {
                    v___x_3148_ = v___x_3145_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
                    v___x_3148_ = v_reuseFailAlloc_3149_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3148_;
            }
            21 => {
                if crate::leanh::lean_obj_tag(v___y_3154_) == 0 {
                    v_a_3155_ = crate::leanh::lean_ctor_get(v___y_3154_, 0);
                    crate::leanh::lean_inc(v_a_3155_);
                    crate::leanh::lean_dec_ref_known(v___y_3154_, 1);
                    v___y_3091_ = v___y_3152_;
                    v___y_3092_ = v___y_3153_;
                    v_a_3093_ = v_a_3155_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3153_);
                    crate::leanh::lean_dec_ref(v___y_3152_);
                    crate::leanh::lean_del_object(v___x_3083_);
                    v_a_3156_ = crate::leanh::lean_ctor_get(v___y_3154_, 0);
                    v_isSharedCheck_3163_ = (!crate::leanh::lean_is_exclusive(v___y_3154_)) as u8;
                    if v_isSharedCheck_3163_ == 0 {
                        v___x_3158_ = v___y_3154_;
                        v_isShared_3159_ = v_isSharedCheck_3163_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3156_);
                        crate::leanh::lean_dec(v___y_3154_);
                        v___x_3158_ = crate::leanh::lean_box(0);
                        v_isShared_3159_ = v_isSharedCheck_3163_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_3159_ == 0 {
                    v___x_3161_ = v___x_3158_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
                    v___x_3161_ = v_reuseFailAlloc_3162_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3161_;
            }
            24 => {
                if v_a_3165_ == 0 {
                    crate::leanh::lean_del_object(v___x_3078_);
                    v___x_3166_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(v_snd_3062_, v___y_3052_);
                    v_a_3167_ = crate::leanh::lean_ctor_get(v___x_3166_, 0);
                    crate::leanh::lean_inc(v_a_3167_);
                    crate::leanh::lean_dec_ref(v___x_3166_);
                    v___x_3168_ = l_Lean_mkAppN(v_proof_3050_, v_fst_3061_);
                    v___x_3169_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__3___redArg(v___x_3168_, v___y_3052_);
                    v_a_3170_ = crate::leanh::lean_ctor_get(v___x_3169_, 0);
                    crate::leanh::lean_inc(v_a_3170_);
                    crate::leanh::lean_dec_ref(v___x_3169_);
                    v___x_3171_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_topsortMVars_x3f___closed__0;
                    v___x_3172_ = lean_nat_dec_lt(v___x_3067_, v___x_3066_);
                    if v___x_3172_ == 0 {
                        crate::leanh::lean_dec(v_fst_3061_);
                        v___y_3091_ = v_a_3167_;
                        v___y_3092_ = v_a_3170_;
                        v_a_3093_ = v___x_3171_;
                        state = 7;
                        continue;
                    } else {
                        v___x_3173_ = lean_nat_dec_le(v___x_3066_, v___x_3066_);
                        if v___x_3173_ == 0 {
                            if v___x_3172_ == 0 {
                                crate::leanh::lean_dec(v_fst_3061_);
                                v___y_3091_ = v_a_3167_;
                                v___y_3092_ = v_a_3170_;
                                v_a_3093_ = v___x_3171_;
                                state = 7;
                                continue;
                            } else {
                                v___x_3174_ = lean_usize_of_nat(v___x_3066_);
                                v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(v_fst_3061_, v___x_3074_, v___x_3174_, v___x_3171_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
                                crate::leanh::lean_dec(v_fst_3061_);
                                v___y_3152_ = v_a_3167_;
                                v___y_3153_ = v_a_3170_;
                                v___y_3154_ = v___x_3175_;
                                state = 21;
                                continue;
                            }
                        } else {
                            v___x_3176_ = lean_usize_of_nat(v___x_3066_);
                            v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__4(v_fst_3061_, v___x_3074_, v___x_3176_, v___x_3171_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
                            crate::leanh::lean_dec(v_fst_3061_);
                            v___y_3152_ = v_a_3167_;
                            v___y_3153_ = v_a_3170_;
                            v___y_3154_ = v___x_3177_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3083_);
                    crate::leanh::lean_dec(v_snd_3062_);
                    crate::leanh::lean_dec(v_fst_3061_);
                    crate::leanh::lean_dec_ref(v_proof_3050_);
                    if v_isShared_3079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3078_, 0, v___x_3069_);
                        v___x_3179_ = v___x_3078_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3069_);
                        v___x_3179_ = v_reuseFailAlloc_3180_;
                        state = 25;
                        continue;
                    }
                }
            }
            25 => {
                return v___x_3179_;
            }
            26 => {
                if v_isShared_3189_ == 0 {
                    v___x_3191_ = v___x_3188_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
                    v___x_3191_ = v_reuseFailAlloc_3192_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3191_;
            }
            28 => {
                return v___x_3198_;
            }
            29 => {
                if v_isShared_3204_ == 0 {
                    v___x_3206_ = v___x_3203_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3206_;
            }
            31 => {
                return v___x_3212_;
            }
            32 => {
                if v_isShared_3219_ == 0 {
                    v___x_3221_ = v___x_3218_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0___boxed(
    mut v_prop_3224_: *mut crate::leanh::LeanObject,
    mut v_proof_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
    mut v___y_3227_: *mut crate::leanh::LeanObject,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3231_ =
        l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0(
            v_prop_3224_,
            v_proof_3225_,
            v___y_3226_,
            v___y_3227_,
            v___y_3228_,
            v___y_3229_,
        );
    crate::leanh::lean_dec(v___y_3229_);
    crate::leanh::lean_dec_ref(v___y_3228_);
    crate::leanh::lean_dec(v___y_3227_);
    crate::leanh::lean_dec_ref(v___y_3226_);
    return v_res_3231_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(
    mut v_prop_3232_: *mut crate::leanh::LeanObject,
    mut v_proof_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3239_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___lam__0___boxed as *mut core::ffi::c_void, 7, 2);
    crate::leanh::lean_closure_set(v___f_3239_, 0, v_prop_3232_);
    crate::leanh::lean_closure_set(v___f_3239_, 1, v_proof_3233_);
    v___x_3240_ = 0;
    v___x_3241_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__6___redArg(v___f_3239_, v___x_3240_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
    return v___x_3241_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore___boxed(
    mut v_prop_3242_: *mut crate::leanh::LeanObject,
    mut v_proof_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3249_ = l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(
        v_prop_3242_,
        v_proof_3243_,
        v_a_3244_,
        v_a_3245_,
        v_a_3246_,
        v_a_3247_,
    );
    crate::leanh::lean_dec(v_a_3247_);
    crate::leanh::lean_dec_ref(v_a_3246_);
    crate::leanh::lean_dec(v_a_3245_);
    crate::leanh::lean_dec_ref(v_a_3244_);
    return v_res_3249_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(
    mut v_mvarId_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___redArg(v_mvarId_3250_, v___y_3252_);
    return v___x_3256_;
}
pub unsafe fn l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0___boxed(
    mut v_mvarId_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
    mut v___y_3260_: *mut crate::leanh::LeanObject,
    mut v___y_3261_: *mut crate::leanh::LeanObject,
    mut v___y_3262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3263_ = l_Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0(v_mvarId_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
    crate::leanh::lean_dec(v___y_3261_);
    crate::leanh::lean_dec_ref(v___y_3260_);
    crate::leanh::lean_dec(v___y_3259_);
    crate::leanh::lean_dec_ref(v___y_3258_);
    crate::leanh::lean_dec(v_mvarId_3257_);
    return v_res_3263_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(
    mut v_mvarId_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3270_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___redArg(v_mvarId_3264_, v___y_3266_);
    return v___x_3270_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2___boxed(
    mut v_mvarId_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
    mut v___y_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3277_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__2(v_mvarId_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
    crate::leanh::lean_dec(v___y_3275_);
    crate::leanh::lean_dec_ref(v___y_3274_);
    crate::leanh::lean_dec(v___y_3273_);
    crate::leanh::lean_dec_ref(v___y_3272_);
    crate::leanh::lean_dec(v_mvarId_3271_);
    return v_res_3277_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0(
    mut v_00_u03b2_3278_: *mut crate::leanh::LeanObject,
    mut v_x_3279_: *mut crate::leanh::LeanObject,
    mut v_x_3280_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3281_: u8 = 0;
    v___x_3281_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___redArg(v_x_3279_, v_x_3280_);
    return v___x_3281_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0___boxed(
    mut v_00_u03b2_3282_: *mut crate::leanh::LeanObject,
    mut v_x_3283_: *mut crate::leanh::LeanObject,
    mut v_x_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3285_: u8 = 0;
    let mut v_r_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3285_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0(v_00_u03b2_3282_, v_x_3283_, v_x_3284_);
    crate::leanh::lean_dec(v_x_3284_);
    crate::leanh::lean_dec_ref(v_x_3283_);
    v_r_3286_ = crate::leanh::lean_box((v_res_3285_) as usize);
    return v_r_3286_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3(
    mut v_00_u03b2_3287_: *mut crate::leanh::LeanObject,
    mut v_x_3288_: *mut crate::leanh::LeanObject,
    mut v_x_3289_: usize,
    mut v_x_3290_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3291_: u8 = 0;
    v___x_3291_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___redArg(v_x_3288_, v_x_3289_, v_x_3290_);
    return v___x_3291_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b2_3292_: *mut crate::leanh::LeanObject,
    mut v_x_3293_: *mut crate::leanh::LeanObject,
    mut v_x_3294_: *mut crate::leanh::LeanObject,
    mut v_x_3295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_10142__boxed_3296_: usize = 0;
    let mut v_res_3297_: u8 = 0;
    let mut v_r_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_10142__boxed_3296_ = crate::leanh::lean_unbox_usize(v_x_3294_);
    crate::leanh::lean_dec(v_x_3294_);
    v_res_3297_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3(v_00_u03b2_3292_, v_x_3293_, v_x_10142__boxed_3296_, v_x_3295_);
    crate::leanh::lean_dec(v_x_3295_);
    crate::leanh::lean_dec_ref(v_x_3293_);
    v_r_3298_ = crate::leanh::lean_box((v_res_3297_) as usize);
    return v_r_3298_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8(
    mut v_00_u03b2_3299_: *mut crate::leanh::LeanObject,
    mut v_keys_3300_: *mut crate::leanh::LeanObject,
    mut v_vals_3301_: *mut crate::leanh::LeanObject,
    mut v_heq_3302_: *mut crate::leanh::LeanObject,
    mut v_i_3303_: *mut crate::leanh::LeanObject,
    mut v_k_3304_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3305_: u8 = 0;
    v___x_3305_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___redArg(v_keys_3300_, v_i_3303_, v_k_3304_);
    return v___x_3305_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8___boxed(
    mut v_00_u03b2_3306_: *mut crate::leanh::LeanObject,
    mut v_keys_3307_: *mut crate::leanh::LeanObject,
    mut v_vals_3308_: *mut crate::leanh::LeanObject,
    mut v_heq_3309_: *mut crate::leanh::LeanObject,
    mut v_i_3310_: *mut crate::leanh::LeanObject,
    mut v_k_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3312_: u8 = 0;
    let mut v_r_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3312_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isDelayedAssigned___at___00__private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_3306_, v_keys_3307_, v_vals_3308_, v_heq_3309_, v_i_3310_, v_k_3311_);
    crate::leanh::lean_dec(v_k_3311_);
    crate::leanh::lean_dec_ref(v_vals_3308_);
    crate::leanh::lean_dec_ref(v_keys_3307_);
    v_r_3313_ = crate::leanh::lean_box((v_res_3312_) as usize);
    return v_r_3313_;
}
pub unsafe fn l_Lean_Meta_Grind_eqResolution___lam__0(
    mut v_prop_3314_: *mut crate::leanh::LeanObject,
    mut v_h_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v_val_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3329_: u8 = 0;
    let mut v_fst_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3334_: u8 = 0;
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: u8 = 0;
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3345_: u8 = 0;
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v_a_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_h_3315_);
                v___x_3321_ =
                    l___private_Lean_Meta_Tactic_Grind_EqResolution_0__Lean_Meta_Grind_eqResCore(
                        v_prop_3314_,
                        v_h_3315_,
                        v___y_3316_,
                        v___y_3317_,
                        v___y_3318_,
                        v___y_3319_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3321_) == 0 {
                    v_a_3322_ = crate::leanh::lean_ctor_get(v___x_3321_, 0);
                    v_isSharedCheck_3370_ = (!crate::leanh::lean_is_exclusive(v___x_3321_)) as u8;
                    if v_isSharedCheck_3370_ == 0 {
                        v___x_3324_ = v___x_3321_;
                        v_isShared_3325_ = v_isSharedCheck_3370_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3322_);
                        crate::leanh::lean_dec(v___x_3321_);
                        v___x_3324_ = crate::leanh::lean_box(0);
                        v_isShared_3325_ = v_isSharedCheck_3370_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_3315_);
                    return v___x_3321_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3322_) == 1 {
                    crate::leanh::lean_del_object(v___x_3324_);
                    v_val_3326_ = crate::leanh::lean_ctor_get(v_a_3322_, 0);
                    v_isSharedCheck_3365_ = (!crate::leanh::lean_is_exclusive(v_a_3322_)) as u8;
                    if v_isSharedCheck_3365_ == 0 {
                        v___x_3328_ = v_a_3322_;
                        v_isShared_3329_ = v_isSharedCheck_3365_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3326_);
                        crate::leanh::lean_dec(v_a_3322_);
                        v___x_3328_ = crate::leanh::lean_box(0);
                        v_isShared_3329_ = v_isSharedCheck_3365_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3322_);
                    crate::leanh::lean_dec_ref(v_h_3315_);
                    v___x_3366_ = crate::leanh::lean_box(0);
                    if v_isShared_3325_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3324_, 0, v___x_3366_);
                        v___x_3368_ = v___x_3324_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3366_);
                        v___x_3368_ = v_reuseFailAlloc_3369_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3330_ = crate::leanh::lean_ctor_get(v_val_3326_, 0);
                v_snd_3331_ = crate::leanh::lean_ctor_get(v_val_3326_, 1);
                v_isSharedCheck_3364_ = (!crate::leanh::lean_is_exclusive(v_val_3326_)) as u8;
                if v_isSharedCheck_3364_ == 0 {
                    v___x_3333_ = v_val_3326_;
                    v_isShared_3334_ = v_isSharedCheck_3364_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3331_);
                    crate::leanh::lean_inc(v_fst_3330_);
                    crate::leanh::lean_dec(v_val_3326_);
                    v___x_3333_ = crate::leanh::lean_box(0);
                    v_isShared_3334_ = v_isSharedCheck_3364_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3335_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3336_ = lean_mk_empty_array_with_capacity(v___x_3335_);
                v___x_3337_ = lean_array_push(v___x_3336_, v_h_3315_);
                v___x_3338_ = 0;
                v___x_3339_ = 1;
                v___x_3340_ = 1;
                v___x_3341_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_3337_,
                    v_snd_3331_,
                    v___x_3338_,
                    v___x_3339_,
                    v___x_3338_,
                    v___x_3339_,
                    v___x_3340_,
                    v___y_3316_,
                    v___y_3317_,
                    v___y_3318_,
                    v___y_3319_,
                );
                crate::leanh::lean_dec_ref(v___x_3337_);
                if crate::leanh::lean_obj_tag(v___x_3341_) == 0 {
                    v_a_3342_ = crate::leanh::lean_ctor_get(v___x_3341_, 0);
                    v_isSharedCheck_3355_ = (!crate::leanh::lean_is_exclusive(v___x_3341_)) as u8;
                    if v_isSharedCheck_3355_ == 0 {
                        v___x_3344_ = v___x_3341_;
                        v_isShared_3345_ = v_isSharedCheck_3355_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3342_);
                        crate::leanh::lean_dec(v___x_3341_);
                        v___x_3344_ = crate::leanh::lean_box(0);
                        v_isShared_3345_ = v_isSharedCheck_3355_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3333_);
                    crate::leanh::lean_dec(v_fst_3330_);
                    crate::leanh::lean_del_object(v___x_3328_);
                    v_a_3356_ = crate::leanh::lean_ctor_get(v___x_3341_, 0);
                    v_isSharedCheck_3363_ = (!crate::leanh::lean_is_exclusive(v___x_3341_)) as u8;
                    if v_isSharedCheck_3363_ == 0 {
                        v___x_3358_ = v___x_3341_;
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3356_);
                        crate::leanh::lean_dec(v___x_3341_);
                        v___x_3358_ = crate::leanh::lean_box(0);
                        v_isShared_3359_ = v_isSharedCheck_3363_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3333_, 1, v_a_3342_);
                    v___x_3347_ = v___x_3333_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_fst_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3342_);
                    v___x_3347_ = v_reuseFailAlloc_3354_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3329_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3328_, 0, v___x_3347_);
                    v___x_3349_ = v___x_3328_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3347_);
                    v___x_3349_ = v_reuseFailAlloc_3353_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3344_, 0, v___x_3349_);
                    v___x_3351_ = v___x_3344_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
                    v___x_3351_ = v_reuseFailAlloc_3352_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3351_;
            }
            8 => {
                if v_isShared_3359_ == 0 {
                    v___x_3361_ = v___x_3358_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
                    v___x_3361_ = v_reuseFailAlloc_3362_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3361_;
            }
            10 => {
                return v___x_3368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_eqResolution___lam__0___boxed(
    mut v_prop_3371_: *mut crate::leanh::LeanObject,
    mut v_h_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
    mut v___y_3376_: *mut crate::leanh::LeanObject,
    mut v___y_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Lean_Meta_Grind_eqResolution___lam__0(
        v_prop_3371_,
        v_h_3372_,
        v___y_3373_,
        v___y_3374_,
        v___y_3375_,
        v___y_3376_,
    );
    crate::leanh::lean_dec(v___y_3376_);
    crate::leanh::lean_dec_ref(v___y_3375_);
    crate::leanh::lean_dec(v___y_3374_);
    crate::leanh::lean_dec_ref(v___y_3373_);
    return v_res_3378_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0(
    mut v_k_3379_: *mut crate::leanh::LeanObject,
    mut v_b_3380_: *mut crate::leanh::LeanObject,
    mut v___y_3381_: *mut crate::leanh::LeanObject,
    mut v___y_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3384_);
    crate::leanh::lean_inc_ref(v___y_3383_);
    crate::leanh::lean_inc(v___y_3382_);
    crate::leanh::lean_inc_ref(v___y_3381_);
    v___x_3386_ = crate::leanh::lean_apply_6(
        v_k_3379_,
        v_b_3380_,
        v___y_3381_,
        v___y_3382_,
        v___y_3383_,
        v___y_3384_,
        crate::leanh::lean_box(0),
    );
    return v___x_3386_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3387_: *mut crate::leanh::LeanObject,
    mut v_b_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3394_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0(v_k_3387_, v_b_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
    crate::leanh::lean_dec(v___y_3392_);
    crate::leanh::lean_dec_ref(v___y_3391_);
    crate::leanh::lean_dec(v___y_3390_);
    crate::leanh::lean_dec_ref(v___y_3389_);
    return v_res_3394_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(
    mut v_name_3395_: *mut crate::leanh::LeanObject,
    mut v_bi_3396_: u8,
    mut v_type_3397_: *mut crate::leanh::LeanObject,
    mut v_k_3398_: *mut crate::leanh::LeanObject,
    mut v_kind_3399_: u8,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
    mut v___y_3403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut v_a_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3418_: u8 = 0;
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3405_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_3405_, 0, v_k_3398_);
                v___x_3406_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3395_,
                    v_bi_3396_,
                    v_type_3397_,
                    v___f_3405_,
                    v_kind_3399_,
                    v___y_3400_,
                    v___y_3401_,
                    v___y_3402_,
                    v___y_3403_,
                );
                if crate::leanh::lean_obj_tag(v___x_3406_) == 0 {
                    v_a_3407_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3414_ = (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3414_ == 0 {
                        v___x_3409_ = v___x_3406_;
                        v_isShared_3410_ = v_isSharedCheck_3414_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3407_);
                        crate::leanh::lean_dec(v___x_3406_);
                        v___x_3409_ = crate::leanh::lean_box(0);
                        v_isShared_3410_ = v_isSharedCheck_3414_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3415_ = crate::leanh::lean_ctor_get(v___x_3406_, 0);
                    v_isSharedCheck_3422_ = (!crate::leanh::lean_is_exclusive(v___x_3406_)) as u8;
                    if v_isSharedCheck_3422_ == 0 {
                        v___x_3417_ = v___x_3406_;
                        v_isShared_3418_ = v_isSharedCheck_3422_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3415_);
                        crate::leanh::lean_dec(v___x_3406_);
                        v___x_3417_ = crate::leanh::lean_box(0);
                        v_isShared_3418_ = v_isSharedCheck_3422_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3410_ == 0 {
                    v___x_3412_ = v___x_3409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
                    v___x_3412_ = v_reuseFailAlloc_3413_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3412_;
            }
            3 => {
                if v_isShared_3418_ == 0 {
                    v___x_3420_ = v___x_3417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
                    v___x_3420_ = v_reuseFailAlloc_3421_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg___boxed(
    mut v_name_3423_: *mut crate::leanh::LeanObject,
    mut v_bi_3424_: *mut crate::leanh::LeanObject,
    mut v_type_3425_: *mut crate::leanh::LeanObject,
    mut v_k_3426_: *mut crate::leanh::LeanObject,
    mut v_kind_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
    mut v___y_3432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3433_: u8 = 0;
    let mut v_kind_boxed_3434_: u8 = 0;
    let mut v_res_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3433_ = (crate::leanh::lean_unbox(v_bi_3424_) as u8);
    v_kind_boxed_3434_ = (crate::leanh::lean_unbox(v_kind_3427_) as u8);
    v_res_3435_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(v_name_3423_, v_bi_boxed_3433_, v_type_3425_, v_k_3426_, v_kind_boxed_3434_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
    crate::leanh::lean_dec(v___y_3431_);
    crate::leanh::lean_dec_ref(v___y_3430_);
    crate::leanh::lean_dec(v___y_3429_);
    crate::leanh::lean_dec_ref(v___y_3428_);
    return v_res_3435_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(
    mut v_name_3436_: *mut crate::leanh::LeanObject,
    mut v_type_3437_: *mut crate::leanh::LeanObject,
    mut v_k_3438_: *mut crate::leanh::LeanObject,
    mut v___y_3439_: *mut crate::leanh::LeanObject,
    mut v___y_3440_: *mut crate::leanh::LeanObject,
    mut v___y_3441_: *mut crate::leanh::LeanObject,
    mut v___y_3442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3444_: u8 = 0;
    let mut v___x_3445_: u8 = 0;
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ = 0;
    v___x_3445_ = 0;
    v___x_3446_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(v_name_3436_, v___x_3444_, v_type_3437_, v_k_3438_, v___x_3445_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
    return v___x_3446_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg___boxed(
    mut v_name_3447_: *mut crate::leanh::LeanObject,
    mut v_type_3448_: *mut crate::leanh::LeanObject,
    mut v_k_3449_: *mut crate::leanh::LeanObject,
    mut v___y_3450_: *mut crate::leanh::LeanObject,
    mut v___y_3451_: *mut crate::leanh::LeanObject,
    mut v___y_3452_: *mut crate::leanh::LeanObject,
    mut v___y_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3455_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(
        v_name_3447_,
        v_type_3448_,
        v_k_3449_,
        v___y_3450_,
        v___y_3451_,
        v___y_3452_,
        v___y_3453_,
    );
    crate::leanh::lean_dec(v___y_3453_);
    crate::leanh::lean_dec_ref(v___y_3452_);
    crate::leanh::lean_dec(v___y_3451_);
    crate::leanh::lean_dec_ref(v___y_3450_);
    return v_res_3455_;
}
pub unsafe fn l_Lean_Meta_Grind_eqResolution(
    mut v_prop_3459_: *mut crate::leanh::LeanObject,
    mut v_a_3460_: *mut crate::leanh::LeanObject,
    mut v_a_3461_: *mut crate::leanh::LeanObject,
    mut v_a_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_prop_3459_);
    v___f_3465_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_eqResolution___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3465_, 0, v_prop_3459_);
    v___x_3466_ = l_Lean_Meta_Grind_eqResolution___closed__1;
    v___x_3467_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(
        v___x_3466_,
        v_prop_3459_,
        v___f_3465_,
        v_a_3460_,
        v_a_3461_,
        v_a_3462_,
        v_a_3463_,
    );
    return v___x_3467_;
}
pub unsafe fn l_Lean_Meta_Grind_eqResolution___boxed(
    mut v_prop_3468_: *mut crate::leanh::LeanObject,
    mut v_a_3469_: *mut crate::leanh::LeanObject,
    mut v_a_3470_: *mut crate::leanh::LeanObject,
    mut v_a_3471_: *mut crate::leanh::LeanObject,
    mut v_a_3472_: *mut crate::leanh::LeanObject,
    mut v_a_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3474_ =
        l_Lean_Meta_Grind_eqResolution(v_prop_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
    crate::leanh::lean_dec(v_a_3472_);
    crate::leanh::lean_dec_ref(v_a_3471_);
    crate::leanh::lean_dec(v_a_3470_);
    crate::leanh::lean_dec_ref(v_a_3469_);
    return v_res_3474_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0(
    mut v_00_u03b1_3475_: *mut crate::leanh::LeanObject,
    mut v_name_3476_: *mut crate::leanh::LeanObject,
    mut v_bi_3477_: u8,
    mut v_type_3478_: *mut crate::leanh::LeanObject,
    mut v_k_3479_: *mut crate::leanh::LeanObject,
    mut v_kind_3480_: u8,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___redArg(v_name_3476_, v_bi_3477_, v_type_3478_, v_k_3479_, v_kind_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
    return v___x_3486_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0___boxed(
    mut v_00_u03b1_3487_: *mut crate::leanh::LeanObject,
    mut v_name_3488_: *mut crate::leanh::LeanObject,
    mut v_bi_3489_: *mut crate::leanh::LeanObject,
    mut v_type_3490_: *mut crate::leanh::LeanObject,
    mut v_k_3491_: *mut crate::leanh::LeanObject,
    mut v_kind_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3498_: u8 = 0;
    let mut v_kind_boxed_3499_: u8 = 0;
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3498_ = (crate::leanh::lean_unbox(v_bi_3489_) as u8);
    v_kind_boxed_3499_ = (crate::leanh::lean_unbox(v_kind_3492_) as u8);
    v_res_3500_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0_spec__0(v_00_u03b1_3487_, v_name_3488_, v_bi_boxed_3498_, v_type_3490_, v_k_3491_, v_kind_boxed_3499_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
    crate::leanh::lean_dec(v___y_3496_);
    crate::leanh::lean_dec_ref(v___y_3495_);
    crate::leanh::lean_dec(v___y_3494_);
    crate::leanh::lean_dec_ref(v___y_3493_);
    return v_res_3500_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0(
    mut v_00_u03b1_3501_: *mut crate::leanh::LeanObject,
    mut v_name_3502_: *mut crate::leanh::LeanObject,
    mut v_type_3503_: *mut crate::leanh::LeanObject,
    mut v_k_3504_: *mut crate::leanh::LeanObject,
    mut v___y_3505_: *mut crate::leanh::LeanObject,
    mut v___y_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3510_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___redArg(
        v_name_3502_,
        v_type_3503_,
        v_k_3504_,
        v___y_3505_,
        v___y_3506_,
        v___y_3507_,
        v___y_3508_,
    );
    return v___x_3510_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0___boxed(
    mut v_00_u03b1_3511_: *mut crate::leanh::LeanObject,
    mut v_name_3512_: *mut crate::leanh::LeanObject,
    mut v_type_3513_: *mut crate::leanh::LeanObject,
    mut v_k_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
    mut v___y_3516_: *mut crate::leanh::LeanObject,
    mut v___y_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_eqResolution_spec__0(
        v_00_u03b1_3511_,
        v_name_3512_,
        v_type_3513_,
        v_k_3514_,
        v___y_3515_,
        v___y_3516_,
        v___y_3517_,
        v___y_3518_,
    );
    crate::leanh::lean_dec(v___y_3518_);
    crate::leanh::lean_dec_ref(v___y_3517_);
    crate::leanh::lean_dec(v___y_3516_);
    crate::leanh::lean_dec_ref(v___y_3515_);
    return v_res_3520_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution(
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
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_EqResolution(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_EqResolution(
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
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_MatchUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
}
