// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: Lean.Util.SortExprs Lean.Meta.KExprMap Lean.Data.RArray Lean.Meta.NatInstTesters Lean.Meta.Offset Init.Data.Nat.Linear
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_to_int, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_string_dec_eq, lean_string_length, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, l_Nat_Linear_Expr_inc, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::RArray::{
    initialize_Lean_Data_RArray, l_Lean_RArray_ofArray___redArg, l_Lean_RArray_toExpr___redArg,
    runtime_initialize_Lean_Data_RArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkInstOfNatNat, l_Lean_mkNatAdd, l_Lean_mkNatEq,
    l_Lean_mkNatLE, l_Lean_mkNatLit, l_Lean_mkNatMul,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isDefEqI,
};
use crate::r#gen::Lean::Meta::KExprMap::{
    initialize_Lean_Meta_KExprMap, l_Lean_Meta_KExprMap_find_x3f___redArg,
    l_Lean_Meta_KExprMap_insert___redArg, runtime_initialize_Lean_Meta_KExprMap,
};
use crate::r#gen::Lean::Meta::NatInstTesters::{
    initialize_Lean_Meta_NatInstTesters, l_Lean_Meta_DefEq_isInstAddNat,
    l_Lean_Meta_DefEq_isInstHAddNat, l_Lean_Meta_DefEq_isInstHMulNat,
    l_Lean_Meta_DefEq_isInstLENat, l_Lean_Meta_DefEq_isInstLTNat, l_Lean_Meta_DefEq_isInstMulNat,
    l_Lean_Meta_Structural_isInstOfNatNat___redArg, runtime_initialize_Lean_Meta_NatInstTesters,
};
use crate::r#gen::Lean::Meta::Offset::{
    initialize_Lean_Meta_Offset, l_Lean_Meta_evalNat, runtime_initialize_Lean_Meta_Offset,
};
use crate::r#gen::Lean::Util::SortExprs::{
    initialize_Lean_Util_SortExprs, l_Lean_sortExprs, runtime_initialize_Lean_Util_SortExprs,
};
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value:
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 110, 117, 109, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value:
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 118, 97, 114, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value:
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 97, 100, 100, 0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value:
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 109, 117, 108, 76,
        0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value:
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
        78, 97, 116, 46, 76, 105, 110, 101, 97, 114, 46, 69, 120, 112, 114, 46, 109, 117, 108, 82,
        0,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value:
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
    m_data: [101, 113, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value:
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
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value:
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
    m_data: [108, 104, 115, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value:
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
    m_data: [114, 104, 115, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value:
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
    m_data: [32, 125, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject] };
static mut l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value:
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
    m_fun: l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value:
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
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value:
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
    m_data: [76, 105, 110, 101, 97, 114, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value:
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
    m_data: [69, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value:
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
    m_data: [110, 117, 109, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
            as *mut leanh::LeanObject,
        5346548721068792964 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value)
            as *mut leanh::LeanObject,
        7684849496198239688 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value:
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
    m_data: [118, 97, 114, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
            as *mut leanh::LeanObject,
        5346548721068792964 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value)
            as *mut leanh::LeanObject,
        18175190525027609149 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value:
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
    m_data: [97, 100, 100, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
            as *mut leanh::LeanObject,
        5346548721068792964 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value)
            as *mut leanh::LeanObject,
        14196997771537767481 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value:
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
    m_data: [109, 117, 108, 76, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
            as *mut leanh::LeanObject,
        5346548721068792964 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value)
            as *mut leanh::LeanObject,
        4793823359960896323 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value:
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
    m_data: [109, 117, 108, 82, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
            as *mut leanh::LeanObject,
        5346548721068792964 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value)
            as *mut leanh::LeanObject,
        15046034327177700902 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value:
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
    m_fun: l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value)
            as *mut leanh::LeanObject,
        5346548721068792964 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value:
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
    m_data: [69, 120, 112, 114, 67, 110, 115, 116, 114, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value:
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
    m_data: [109, 107, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        7629568945124732217 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        15767036023735109173 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value:
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
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value)
            as *mut leanh::LeanObject,
        15761733860085307253 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value)
            as *mut leanh::LeanObject,
        9255189395584251158 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0_value:
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
    m_fun: l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value)
            as *mut leanh::LeanObject,
        7207443721092690486 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        7629568945124732217 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0_value:
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
    m_data: [122, 101, 114, 111, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1_value:
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 117, 99, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value) as *mut leanh::LeanObject,16112798088292836701 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value) as *mut leanh::LeanObject,14305945245784925820 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value) as *mut leanh::LeanObject,17073733886952259026 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value) as *mut leanh::LeanObject,4707481103260653979 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value) as *mut leanh::LeanObject,11383192766313517692 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value) as *mut leanh::LeanObject,17313347264508353403 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value) as *mut leanh::LeanObject,6683391611519377970 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value) as *mut leanh::LeanObject,1611444129324655608 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value:
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
    m_data: [108, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        17284123358135039274 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value:
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
    m_data: [108, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        10778933377320331970 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value:
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value)
            as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value:
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
    m_data: [71, 84, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value:
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
    m_data: [103, 116, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value)
            as *mut leanh::LeanObject,
        2272833755566510320 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value)
            as *mut leanh::LeanObject,
        9426339939459091439 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value:
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
    m_data: [71, 69, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value:
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
    m_data: [103, 101, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value)
            as *mut leanh::LeanObject,
        1755019837031360842 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value
        ) as *mut leanh::LeanObject,
        5555145617058846791 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value:
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
    m_data: [76, 84, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value_aux_0:
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value
        ) as *mut leanh::LeanObject,
        17878876274162330439 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11833570877100518198 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value:
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
    m_data: [76, 69, 0],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value_aux_0:
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
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value
        ) as *mut leanh::LeanObject,
        8347582161988589016 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value)
            as *mut leanh::LeanObject,
        7316284823769321069 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2_value:
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
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0_value:
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
    m_fun: l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(
    mut v_a_1825_: *mut leanh::LeanObject,
    mut v_x_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1826_) == 0 {
                    v___x_1827_ = leanh::lean_box(0);
                    return v___x_1827_;
                } else {
                    v_key_1828_ = leanh::lean_ctor_get(v_x_1826_, 0);
                    v_value_1829_ = leanh::lean_ctor_get(v_x_1826_, 1);
                    v_tail_1830_ = leanh::lean_ctor_get(v_x_1826_, 2);
                    v___x_1831_ = lean_nat_dec_eq(v_key_1828_, v_a_1825_);
                    if v___x_1831_ == 0 {
                        v_x_1826_ = v_tail_1830_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_1829_);
                        v___x_1833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1833_, 0, v_value_1829_);
                        return v___x_1833_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(
    mut v_a_1834_: *mut leanh::LeanObject,
    mut v_x_1835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_1834_, v_x_1835_);
    leanh::lean_dec(v_x_1835_);
    leanh::lean_dec(v_a_1834_);
    return v_res_1836_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(
    mut v_m_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u64 = 0;
    let mut v___x_1842_: u64 = 0;
    let mut v___x_1843_: u64 = 0;
    let mut v_fold_1844_: u64 = 0;
    let mut v___x_1845_: u64 = 0;
    let mut v___x_1846_: u64 = 0;
    let mut v___x_1847_: u64 = 0;
    let mut v___x_1848_: usize = 0;
    let mut v___x_1849_: usize = 0;
    let mut v___x_1850_: usize = 0;
    let mut v___x_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_1839_ = leanh::lean_ctor_get(v_m_1837_, 1);
    v___x_1840_ = lean_array_get_size(v_buckets_1839_);
    v___x_1841_ = lean_uint64_of_nat(v_a_1838_);
    v___x_1842_ = 32u64;
    v___x_1843_ = lean_uint64_shift_right(v___x_1841_, v___x_1842_);
    v_fold_1844_ = lean_uint64_xor(v___x_1841_, v___x_1843_);
    v___x_1845_ = 16u64;
    v___x_1846_ = lean_uint64_shift_right(v_fold_1844_, v___x_1845_);
    v___x_1847_ = lean_uint64_xor(v_fold_1844_, v___x_1846_);
    v___x_1848_ = lean_uint64_to_usize(v___x_1847_);
    v___x_1849_ = lean_usize_of_nat(v___x_1840_);
    v___x_1850_ = 1usize;
    v___x_1851_ = lean_usize_sub(v___x_1849_, v___x_1850_);
    v___x_1852_ = lean_usize_land(v___x_1848_, v___x_1851_);
    v___x_1853_ = lean_array_uget_borrowed(v_buckets_1839_, v___x_1852_);
    v___x_1854_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_1838_, v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(
    mut v_m_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_1855_, v_a_1856_);
    leanh::lean_dec(v_a_1856_);
    leanh::lean_dec_ref(v_m_1855_);
    return v_res_1857_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(
    mut v_perm_1858_: *mut leanh::LeanObject,
    mut v_a_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v_val_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1869_: u8 = 0;
    let mut v_unused_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1881_: u8 = 0;
    let mut v_k_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1886_: u8 = 0;
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v_a_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_a_1859_) {
                0 => {
                    return v_a_1859_;
                }
                1 => {
                    v_i_1860_ = leanh::lean_ctor_get(v_a_1859_, 0);
                    v___x_1861_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_1858_, v_i_1860_);
                    if leanh::lean_obj_tag(v___x_1861_) == 0 {
                        return v_a_1859_;
                    } else {
                        v_isSharedCheck_1869_ = (!leanh::lean_is_exclusive(v_a_1859_)) as u8;
                        if v_isSharedCheck_1869_ == 0 {
                            v_unused_1870_ = leanh::lean_ctor_get(v_a_1859_, 0);
                            leanh::lean_dec(v_unused_1870_);
                            v___x_1863_ = v_a_1859_;
                            v_isShared_1864_ = v_isSharedCheck_1869_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1859_);
                            v___x_1863_ = leanh::lean_box(0);
                            v_isShared_1864_ = v_isSharedCheck_1869_;
                            state = 1;
                            continue;
                        }
                    }
                }
                2 => {
                    v_a_1871_ = leanh::lean_ctor_get(v_a_1859_, 0);
                    v_b_1872_ = leanh::lean_ctor_get(v_a_1859_, 1);
                    v_isSharedCheck_1881_ = (!leanh::lean_is_exclusive(v_a_1859_)) as u8;
                    if v_isSharedCheck_1881_ == 0 {
                        v___x_1874_ = v_a_1859_;
                        v_isShared_1875_ = v_isSharedCheck_1881_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_b_1872_);
                        leanh::lean_inc(v_a_1871_);
                        leanh::lean_dec(v_a_1859_);
                        v___x_1874_ = leanh::lean_box(0);
                        v_isShared_1875_ = v_isSharedCheck_1881_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_k_1882_ = leanh::lean_ctor_get(v_a_1859_, 0);
                    v_a_1883_ = leanh::lean_ctor_get(v_a_1859_, 1);
                    v_isSharedCheck_1891_ = (!leanh::lean_is_exclusive(v_a_1859_)) as u8;
                    if v_isSharedCheck_1891_ == 0 {
                        v___x_1885_ = v_a_1859_;
                        v_isShared_1886_ = v_isSharedCheck_1891_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1883_);
                        leanh::lean_inc(v_k_1882_);
                        leanh::lean_dec(v_a_1859_);
                        v___x_1885_ = leanh::lean_box(0);
                        v_isShared_1886_ = v_isSharedCheck_1891_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_a_1892_ = leanh::lean_ctor_get(v_a_1859_, 0);
                    v_k_1893_ = leanh::lean_ctor_get(v_a_1859_, 1);
                    v_isSharedCheck_1901_ = (!leanh::lean_is_exclusive(v_a_1859_)) as u8;
                    if v_isSharedCheck_1901_ == 0 {
                        v___x_1895_ = v_a_1859_;
                        v_isShared_1896_ = v_isSharedCheck_1901_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_1893_);
                        leanh::lean_inc(v_a_1892_);
                        leanh::lean_dec(v_a_1859_);
                        v___x_1895_ = leanh::lean_box(0);
                        v_isShared_1896_ = v_isSharedCheck_1901_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_val_1865_ = leanh::lean_ctor_get(v___x_1861_, 0);
                leanh::lean_inc(v_val_1865_);
                leanh::lean_dec_ref_known(v___x_1861_, 1);
                if v_isShared_1864_ == 0 {
                    leanh::lean_ctor_set(v___x_1863_, 0, v_val_1865_);
                    v___x_1867_ = v___x_1863_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_val_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1867_;
            }
            3 => {
                v___x_1876_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_a_1871_);
                v___x_1877_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_b_1872_);
                if v_isShared_1875_ == 0 {
                    leanh::lean_ctor_set(v___x_1874_, 1, v___x_1877_);
                    leanh::lean_ctor_set(v___x_1874_, 0, v___x_1876_);
                    v___x_1879_ = v___x_1874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1877_);
                    v___x_1879_ = v_reuseFailAlloc_1880_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1879_;
            }
            5 => {
                v___x_1887_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_a_1883_);
                if v_isShared_1886_ == 0 {
                    leanh::lean_ctor_set(v___x_1885_, 1, v___x_1887_);
                    v___x_1889_ = v___x_1885_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_k_1882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 1, v___x_1887_);
                    v___x_1889_ = v_reuseFailAlloc_1890_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1889_;
            }
            7 => {
                v___x_1897_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1858_, v_a_1892_);
                if v_isShared_1896_ == 0 {
                    leanh::lean_ctor_set(v___x_1895_, 0, v___x_1897_);
                    v___x_1899_ = v___x_1895_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1900_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_k_1893_);
                    v___x_1899_ = v_reuseFailAlloc_1900_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go___boxed(
    mut v_perm_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(
        v_perm_1902_,
        v_a_1903_,
    );
    leanh::lean_dec_ref(v_perm_1902_);
    return v_res_1904_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(
    mut v_00_u03b2_1905_: *mut leanh::LeanObject,
    mut v_m_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1908_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_1906_, v_a_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___boxed(
    mut v_00_u03b2_1909_: *mut leanh::LeanObject,
    mut v_m_1910_: *mut leanh::LeanObject,
    mut v_a_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1912_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_1909_, v_m_1910_, v_a_1911_);
    leanh::lean_dec(v_a_1911_);
    leanh::lean_dec_ref(v_m_1910_);
    return v_res_1912_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(
    mut v_00_u03b2_1913_: *mut leanh::LeanObject,
    mut v_a_1914_: *mut leanh::LeanObject,
    mut v_x_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_1914_, v_x_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_1917_: *mut leanh::LeanObject,
    mut v_a_1918_: *mut leanh::LeanObject,
    mut v_x_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_1917_, v_a_1918_, v_x_1919_);
    leanh::lean_dec(v_x_1919_);
    leanh::lean_dec(v_a_1918_);
    return v_res_1920_;
}
pub unsafe fn l_Nat_Linear_Expr_applyPerm(
    mut v_perm_1921_: *mut leanh::LeanObject,
    mut v_e_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1923_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(
        v_perm_1921_,
        v_e_1922_,
    );
    return v___x_1923_;
}
pub unsafe fn l_Nat_Linear_Expr_applyPerm___boxed(
    mut v_perm_1924_: *mut leanh::LeanObject,
    mut v_e_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Nat_Linear_Expr_applyPerm(v_perm_1924_, v_e_1925_);
    leanh::lean_dec_ref(v_perm_1924_);
    return v_res_1926_;
}
pub unsafe fn l_Nat_Linear_ExprCnstr_applyPerm(
    mut v_perm_1927_: *mut leanh::LeanObject,
    mut v_x_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eq_1929_: u8 = 0;
    let mut v_lhs_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1929_ = leanh::lean_ctor_get_uint8(
                    v_x_1928_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1930_ = leanh::lean_ctor_get(v_x_1928_, 0);
                v_rhs_1931_ = leanh::lean_ctor_get(v_x_1928_, 1);
                v_isSharedCheck_1940_ = (!leanh::lean_is_exclusive(v_x_1928_)) as u8;
                if v_isSharedCheck_1940_ == 0 {
                    v___x_1933_ = v_x_1928_;
                    v_isShared_1934_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_1931_);
                    leanh::lean_inc(v_lhs_1930_);
                    leanh::lean_dec(v_x_1928_);
                    v___x_1933_ = leanh::lean_box(0);
                    v_isShared_1934_ = v_isSharedCheck_1940_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1935_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1927_, v_lhs_1930_);
                v___x_1936_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_1927_, v_rhs_1931_);
                if v_isShared_1934_ == 0 {
                    leanh::lean_ctor_set(v___x_1933_, 1, v___x_1936_);
                    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1935_);
                    v___x_1938_ = v___x_1933_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1939_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1936_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1939_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_eq_1929_,
                    );
                    v___x_1938_ = v_reuseFailAlloc_1939_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_ExprCnstr_applyPerm___boxed(
    mut v_perm_1941_: *mut leanh::LeanObject,
    mut v_x_1942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Nat_Linear_ExprCnstr_applyPerm(v_perm_1941_, v_x_1942_);
    leanh::lean_dec_ref(v_perm_1941_);
    return v_res_1943_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = leanh::lean_unsigned_to_nat(2);
    v___x_1951_ = lean_nat_to_int(v___x_1950_);
    return v___x_1951_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = leanh::lean_unsigned_to_nat(1);
    v___x_1953_ = lean_nat_to_int(v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(
    mut v_x_1978_: *mut leanh::LeanObject,
    mut v_prec_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v___y_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut v_i_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___y_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_a_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_k_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_a_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1978_) {
                0 => {
                    v_v_1980_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_2000_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2000_ == 0 {
                        v___x_1982_ = v_x_1978_;
                        v_isShared_1983_ = v_isSharedCheck_2000_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1980_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_1982_ = leanh::lean_box(0);
                        v_isShared_1983_ = v_isSharedCheck_2000_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_2001_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_2021_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2021_ == 0 {
                        v___x_2003_ = v_x_1978_;
                        v_isShared_2004_ = v_isSharedCheck_2021_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_2001_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_2003_ = leanh::lean_box(0);
                        v_isShared_2004_ = v_isSharedCheck_2021_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_a_2022_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_b_2023_ = leanh::lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2046_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2025_ = v_x_1978_;
                        v_isShared_2026_ = v_isSharedCheck_2046_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_b_2023_);
                        leanh::lean_inc(v_a_2022_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_2025_ = leanh::lean_box(0);
                        v_isShared_2026_ = v_isSharedCheck_2046_;
                        state = 7;
                        continue;
                    }
                }
                3 => {
                    v_k_2047_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_a_2048_ = leanh::lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2072_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2072_ == 0 {
                        v___x_2050_ = v_x_1978_;
                        v_isShared_2051_ = v_isSharedCheck_2072_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2048_);
                        leanh::lean_inc(v_k_2047_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_2050_ = leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2072_;
                        state = 10;
                        continue;
                    }
                }
                _ => {
                    v_a_2073_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_k_2074_ = leanh::lean_ctor_get(v_x_1978_, 1);
                    v_isSharedCheck_2098_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_2098_ == 0 {
                        v___x_2076_ = v_x_1978_;
                        v_isShared_2077_ = v_isSharedCheck_2098_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_2074_);
                        leanh::lean_inc(v_a_2073_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_2076_ = leanh::lean_box(0);
                        v_isShared_2077_ = v_isSharedCheck_2098_;
                        state = 13;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1996_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1997_ = lean_nat_dec_le(v___x_1996_, v_prec_1979_);
                if v___x_1997_ == 0 {
                    v___x_1998_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_1985_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v___x_1999_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_1985_ = v___x_1999_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1986_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2;
                v___x_1987_ = l_Nat_reprFast(v_v_1980_);
                if v_isShared_1983_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1982_, 3);
                    leanh::lean_ctor_set(v___x_1982_, 0, v___x_1987_);
                    v___x_1989_ = v___x_1982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1987_);
                    v___x_1989_ = v_reuseFailAlloc_1995_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1990_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1990_, 0, v___x_1986_);
                leanh::lean_ctor_set(v___x_1990_, 1, v___x_1989_);
                leanh::lean_inc(v___y_1985_);
                v___x_1991_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1991_, 0, v___y_1985_);
                leanh::lean_ctor_set(v___x_1991_, 1, v___x_1990_);
                v___x_1992_ = 0;
                v___x_1993_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1993_, 0, v___x_1991_);
                leanh::lean_ctor_set_uint8(
                    v___x_1993_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1992_,
                );
                v___x_1994_ = l_Repr_addAppParen(v___x_1993_, v_prec_1979_);
                return v___x_1994_;
            }
            4 => {
                v___x_2017_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2018_ = lean_nat_dec_le(v___x_2017_, v_prec_1979_);
                if v___x_2018_ == 0 {
                    v___x_2019_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2006_ = v___x_2019_;
                    state = 5;
                    continue;
                } else {
                    v___x_2020_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2006_ = v___x_2020_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2007_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7;
                v___x_2008_ = l_Nat_reprFast(v_i_2001_);
                if v_isShared_2004_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2003_, 3);
                    leanh::lean_ctor_set(v___x_2003_, 0, v___x_2008_);
                    v___x_2010_ = v___x_2003_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2008_);
                    v___x_2010_ = v_reuseFailAlloc_2016_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2011_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2011_, 0, v___x_2007_);
                leanh::lean_ctor_set(v___x_2011_, 1, v___x_2010_);
                leanh::lean_inc(v___y_2006_);
                v___x_2012_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2012_, 0, v___y_2006_);
                leanh::lean_ctor_set(v___x_2012_, 1, v___x_2011_);
                v___x_2013_ = 0;
                v___x_2014_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2014_, 0, v___x_2012_);
                leanh::lean_ctor_set_uint8(
                    v___x_2014_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2013_,
                );
                v___x_2015_ = l_Repr_addAppParen(v___x_2014_, v_prec_1979_);
                return v___x_2015_;
            }
            7 => {
                v___x_2027_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2043_ = lean_nat_dec_le(v___x_2027_, v_prec_1979_);
                if v___x_2043_ == 0 {
                    v___x_2044_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2029_ = v___x_2044_;
                    state = 8;
                    continue;
                } else {
                    v___x_2045_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2029_ = v___x_2045_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2030_ = leanh::lean_box(1);
                v___x_2031_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10;
                v___x_2032_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_2022_, v___x_2027_);
                if v_isShared_2026_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2025_, 5);
                    leanh::lean_ctor_set(v___x_2025_, 1, v___x_2032_);
                    leanh::lean_ctor_set(v___x_2025_, 0, v___x_2031_);
                    v___x_2034_ = v___x_2025_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___x_2032_);
                    v___x_2034_ = v_reuseFailAlloc_2042_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2035_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2035_, 0, v___x_2034_);
                leanh::lean_ctor_set(v___x_2035_, 1, v___x_2030_);
                v___x_2036_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_b_2023_, v___x_2027_);
                v___x_2037_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2037_, 0, v___x_2035_);
                leanh::lean_ctor_set(v___x_2037_, 1, v___x_2036_);
                leanh::lean_inc(v___y_2029_);
                v___x_2038_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2038_, 0, v___y_2029_);
                leanh::lean_ctor_set(v___x_2038_, 1, v___x_2037_);
                v___x_2039_ = 0;
                v___x_2040_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2040_, 0, v___x_2038_);
                leanh::lean_ctor_set_uint8(
                    v___x_2040_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2039_,
                );
                v___x_2041_ = l_Repr_addAppParen(v___x_2040_, v_prec_1979_);
                return v___x_2041_;
            }
            10 => {
                v___x_2052_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2069_ = lean_nat_dec_le(v___x_2052_, v_prec_1979_);
                if v___x_2069_ == 0 {
                    v___x_2070_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2054_ = v___x_2070_;
                    state = 11;
                    continue;
                } else {
                    v___x_2071_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2054_ = v___x_2071_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2055_ = leanh::lean_box(1);
                v___x_2056_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13;
                v___x_2057_ = l_Nat_reprFast(v_k_2047_);
                v___x_2058_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2058_, 0, v___x_2057_);
                if v_isShared_2051_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2050_, 5);
                    leanh::lean_ctor_set(v___x_2050_, 1, v___x_2058_);
                    leanh::lean_ctor_set(v___x_2050_, 0, v___x_2056_);
                    v___x_2060_ = v___x_2050_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2068_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2058_);
                    v___x_2060_ = v_reuseFailAlloc_2068_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2061_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2061_, 0, v___x_2060_);
                leanh::lean_ctor_set(v___x_2061_, 1, v___x_2055_);
                v___x_2062_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_2048_, v___x_2052_);
                v___x_2063_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2063_, 0, v___x_2061_);
                leanh::lean_ctor_set(v___x_2063_, 1, v___x_2062_);
                leanh::lean_inc(v___y_2054_);
                v___x_2064_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2064_, 0, v___y_2054_);
                leanh::lean_ctor_set(v___x_2064_, 1, v___x_2063_);
                v___x_2065_ = 0;
                v___x_2066_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2066_, 0, v___x_2064_);
                leanh::lean_ctor_set_uint8(
                    v___x_2066_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2065_,
                );
                v___x_2067_ = l_Repr_addAppParen(v___x_2066_, v_prec_1979_);
                return v___x_2067_;
            }
            13 => {
                v___x_2078_ = leanh::lean_unsigned_to_nat(1024);
                v___x_2095_ = lean_nat_dec_le(v___x_2078_, v_prec_1979_);
                if v___x_2095_ == 0 {
                    v___x_2096_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3,
                    );
                    v___y_2080_ = v___x_2096_;
                    state = 14;
                    continue;
                } else {
                    v___x_2097_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4,
                    );
                    v___y_2080_ = v___x_2097_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2081_ = leanh::lean_box(1);
                v___x_2082_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16;
                v___x_2083_ =
                    l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_2073_, v___x_2078_);
                if v_isShared_2077_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2076_, 5);
                    leanh::lean_ctor_set(v___x_2076_, 1, v___x_2083_);
                    leanh::lean_ctor_set(v___x_2076_, 0, v___x_2082_);
                    v___x_2085_ = v___x_2076_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2094_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2083_);
                    v___x_2085_ = v_reuseFailAlloc_2094_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2086_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2086_, 0, v___x_2085_);
                leanh::lean_ctor_set(v___x_2086_, 1, v___x_2081_);
                v___x_2087_ = l_Nat_reprFast(v_k_2074_);
                v___x_2088_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2088_, 0, v___x_2087_);
                v___x_2089_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2089_, 0, v___x_2086_);
                leanh::lean_ctor_set(v___x_2089_, 1, v___x_2088_);
                leanh::lean_inc(v___y_2080_);
                v___x_2090_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2090_, 0, v___y_2080_);
                leanh::lean_ctor_set(v___x_2090_, 1, v___x_2089_);
                v___x_2091_ = 0;
                v___x_2092_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2092_, 0, v___x_2090_);
                leanh::lean_ctor_set_uint8(
                    v___x_2092_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2091_,
                );
                v___x_2093_ = l_Repr_addAppParen(v___x_2092_, v_prec_1979_);
                return v___x_2093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed(
    mut v_x_2099_: *mut leanh::LeanObject,
    mut v_prec_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_x_2099_, v_prec_2100_);
    leanh::lean_dec(v_prec_2100_);
    return v_res_2101_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr_spec__0(
    mut v_a_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2105_ = lean_nat_to_int(v_a_2104_);
    return v___x_2105_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2119_ = leanh::lean_unsigned_to_nat(6);
    v___x_2120_ = lean_nat_to_int(v___x_2119_);
    return v___x_2120_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = leanh::lean_unsigned_to_nat(7);
    v___x_2128_ = lean_nat_to_int(v___x_2127_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2133_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0;
    v___x_2134_ = lean_string_length(v___x_2133_);
    return v___x_2134_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2135_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16,
    );
    v___x_2136_ = lean_nat_to_int(v___x_2135_);
    return v___x_2136_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(
    mut v_x_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eq_2142_: u8 = 0;
    let mut v_lhs_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eq_2142_ = leanh::lean_ctor_get_uint8(
        v_x_2141_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_lhs_2143_ = leanh::lean_ctor_get(v_x_2141_, 0);
    leanh::lean_inc_ref(v_lhs_2143_);
    v_rhs_2144_ = leanh::lean_ctor_get(v_x_2141_, 1);
    leanh::lean_inc_ref(v_rhs_2144_);
    leanh::lean_dec_ref(v_x_2141_);
    v___x_2145_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
    v___x_2146_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6;
    v___x_2147_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7,
    );
    v___x_2148_ = leanh::lean_unsigned_to_nat(0);
    v___x_2149_ = l_Bool_repr___redArg(v_eq_2142_);
    v___x_2150_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2150_, 0, v___x_2147_);
    leanh::lean_ctor_set(v___x_2150_, 1, v___x_2149_);
    v___x_2151_ = 0;
    v___x_2152_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2152_, 0, v___x_2150_);
    leanh::lean_ctor_set_uint8(
        v___x_2152_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    v___x_2153_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2153_, 0, v___x_2146_);
    leanh::lean_ctor_set(v___x_2153_, 1, v___x_2152_);
    v___x_2154_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
    v___x_2155_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2155_, 0, v___x_2153_);
    leanh::lean_ctor_set(v___x_2155_, 1, v___x_2154_);
    v___x_2156_ = leanh::lean_box(1);
    v___x_2157_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2157_, 0, v___x_2155_);
    leanh::lean_ctor_set(v___x_2157_, 1, v___x_2156_);
    v___x_2158_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11;
    v___x_2159_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2159_, 0, v___x_2157_);
    leanh::lean_ctor_set(v___x_2159_, 1, v___x_2158_);
    v___x_2160_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2160_, 0, v___x_2159_);
    leanh::lean_ctor_set(v___x_2160_, 1, v___x_2145_);
    v___x_2161_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12,
    );
    v___x_2162_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_lhs_2143_, v___x_2148_);
    v___x_2163_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2163_, 0, v___x_2161_);
    leanh::lean_ctor_set(v___x_2163_, 1, v___x_2162_);
    v___x_2164_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2164_, 0, v___x_2163_);
    leanh::lean_ctor_set_uint8(
        v___x_2164_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    v___x_2165_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2165_, 0, v___x_2160_);
    leanh::lean_ctor_set(v___x_2165_, 1, v___x_2164_);
    v___x_2166_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
    leanh::lean_ctor_set(v___x_2166_, 1, v___x_2154_);
    v___x_2167_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2167_, 0, v___x_2166_);
    leanh::lean_ctor_set(v___x_2167_, 1, v___x_2156_);
    v___x_2168_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14;
    v___x_2169_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2169_, 0, v___x_2167_);
    leanh::lean_ctor_set(v___x_2169_, 1, v___x_2168_);
    v___x_2170_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2170_, 0, v___x_2169_);
    leanh::lean_ctor_set(v___x_2170_, 1, v___x_2145_);
    v___x_2171_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_rhs_2144_, v___x_2148_);
    v___x_2172_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2172_, 0, v___x_2161_);
    leanh::lean_ctor_set(v___x_2172_, 1, v___x_2171_);
    v___x_2173_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
    leanh::lean_ctor_set_uint8(
        v___x_2173_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    v___x_2174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2174_, 0, v___x_2170_);
    leanh::lean_ctor_set(v___x_2174_, 1, v___x_2173_);
    v___x_2175_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17,
    );
    v___x_2176_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18;
    v___x_2177_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
    leanh::lean_ctor_set(v___x_2177_, 1, v___x_2174_);
    v___x_2178_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19;
    v___x_2179_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2179_, 0, v___x_2177_);
    leanh::lean_ctor_set(v___x_2179_, 1, v___x_2178_);
    v___x_2180_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2180_, 0, v___x_2175_);
    leanh::lean_ctor_set(v___x_2180_, 1, v___x_2179_);
    v___x_2181_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    leanh::lean_ctor_set_uint8(
        v___x_2181_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2151_,
    );
    return v___x_2181_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(
    mut v_x_2182_: *mut leanh::LeanObject,
    mut v_prec_2183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2184_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(v_x_2182_);
    return v___x_2184_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed(
    mut v_x_2185_: *mut leanh::LeanObject,
    mut v_prec_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(v_x_2185_, v_prec_2186_);
    leanh::lean_dec(v_prec_2186_);
    return v_res_2187_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_2190_: *mut leanh::LeanObject,
    mut v_x_2191_: *mut leanh::LeanObject,
    mut v_x_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2192_) == 0 {
                    leanh::lean_dec(v_x_2190_);
                    return v_x_2191_;
                } else {
                    v_head_2193_ = leanh::lean_ctor_get(v_x_2192_, 0);
                    v_tail_2194_ = leanh::lean_ctor_get(v_x_2192_, 1);
                    v_isSharedCheck_2203_ = (!leanh::lean_is_exclusive(v_x_2192_)) as u8;
                    if v_isSharedCheck_2203_ == 0 {
                        v___x_2196_ = v_x_2192_;
                        v_isShared_2197_ = v_isSharedCheck_2203_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2194_);
                        leanh::lean_inc(v_head_2193_);
                        leanh::lean_dec(v_x_2192_);
                        v___x_2196_ = leanh::lean_box(0);
                        v_isShared_2197_ = v_isSharedCheck_2203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2190_);
                if v_isShared_2197_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2196_, 5);
                    leanh::lean_ctor_set(v___x_2196_, 1, v_x_2190_);
                    leanh::lean_ctor_set(v___x_2196_, 0, v_x_2191_);
                    v___x_2199_ = v___x_2196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_x_2191_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_x_2190_);
                    v___x_2199_ = v_reuseFailAlloc_2202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2200_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                leanh::lean_ctor_set(v___x_2200_, 1, v_head_2193_);
                v_x_2191_ = v___x_2200_;
                v_x_2192_ = v_tail_2194_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(
    mut v_x_2204_: *mut leanh::LeanObject,
    mut v_x_2205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2204_) == 0 {
        let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2205_);
        v___x_2206_ = leanh::lean_box(0);
        return v___x_2206_;
    } else {
        let mut v_tail_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2207_ = leanh::lean_ctor_get(v_x_2204_, 1);
        if leanh::lean_obj_tag(v_tail_2207_) == 0 {
            let mut v_head_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2205_);
            v_head_2208_ = leanh::lean_ctor_get(v_x_2204_, 0);
            leanh::lean_inc(v_head_2208_);
            leanh::lean_dec_ref_known(v_x_2204_, 2);
            return v_head_2208_;
        } else {
            let mut v_head_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2207_);
            v_head_2209_ = leanh::lean_ctor_get(v_x_2204_, 0);
            leanh::lean_inc(v_head_2209_);
            leanh::lean_dec_ref_known(v_x_2204_, 2);
            v___x_2210_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(v_x_2205_, v_head_2209_, v_tail_2207_);
            return v___x_2210_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2216_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0;
    v___x_2217_ = lean_string_length(v___x_2216_);
    return v___x_2217_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2218_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3);
    v___x_2219_ = lean_nat_to_int(v___x_2218_);
    return v___x_2219_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(
    mut v_x_2224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2225_ = leanh::lean_ctor_get(v_x_2224_, 0);
                v_snd_2226_ = leanh::lean_ctor_get(v_x_2224_, 1);
                v_isSharedCheck_2250_ = (!leanh::lean_is_exclusive(v_x_2224_)) as u8;
                if v_isSharedCheck_2250_ == 0 {
                    v___x_2228_ = v_x_2224_;
                    v_isShared_2229_ = v_isSharedCheck_2250_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2226_);
                    leanh::lean_inc(v_fst_2225_);
                    leanh::lean_dec(v_x_2224_);
                    v___x_2228_ = leanh::lean_box(0);
                    v_isShared_2229_ = v_isSharedCheck_2250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2230_ = l_Nat_reprFast(v_fst_2225_);
                v___x_2231_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2231_, 0, v___x_2230_);
                v___x_2232_ = leanh::lean_box(0);
                if v_isShared_2229_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2228_, 1);
                    leanh::lean_ctor_set(v___x_2228_, 1, v___x_2232_);
                    leanh::lean_ctor_set(v___x_2228_, 0, v___x_2231_);
                    v___x_2234_ = v___x_2228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 1, v___x_2232_);
                    v___x_2234_ = v_reuseFailAlloc_2249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2235_ = l_Nat_reprFast(v_snd_2226_);
                v___x_2236_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2236_, 0, v___x_2235_);
                v___x_2237_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2237_, 0, v___x_2236_);
                leanh::lean_ctor_set(v___x_2237_, 1, v___x_2234_);
                v___x_2238_ = l_List_reverse___redArg(v___x_2237_);
                v___x_2239_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
                v___x_2240_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(v___x_2238_, v___x_2239_);
                v___x_2241_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4);
                v___x_2242_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5;
                v___x_2243_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2243_, 0, v___x_2242_);
                leanh::lean_ctor_set(v___x_2243_, 1, v___x_2240_);
                v___x_2244_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6;
                v___x_2245_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2245_, 0, v___x_2243_);
                leanh::lean_ctor_set(v___x_2245_, 1, v___x_2244_);
                v___x_2246_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2246_, 0, v___x_2241_);
                leanh::lean_ctor_set(v___x_2246_, 1, v___x_2245_);
                v___x_2247_ = 0;
                v___x_2248_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2248_, 0, v___x_2246_);
                leanh::lean_ctor_set_uint8(
                    v___x_2248_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2247_,
                );
                return v___x_2248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(
    mut v_x_2251_: *mut leanh::LeanObject,
    mut v_x_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2253_) == 0 {
                    leanh::lean_dec(v_x_2251_);
                    return v_x_2252_;
                } else {
                    v_head_2254_ = leanh::lean_ctor_get(v_x_2253_, 0);
                    v_tail_2255_ = leanh::lean_ctor_get(v_x_2253_, 1);
                    v_isSharedCheck_2265_ = (!leanh::lean_is_exclusive(v_x_2253_)) as u8;
                    if v_isSharedCheck_2265_ == 0 {
                        v___x_2257_ = v_x_2253_;
                        v_isShared_2258_ = v_isSharedCheck_2265_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2255_);
                        leanh::lean_inc(v_head_2254_);
                        leanh::lean_dec(v_x_2253_);
                        v___x_2257_ = leanh::lean_box(0);
                        v_isShared_2258_ = v_isSharedCheck_2265_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2251_);
                if v_isShared_2258_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2257_, 5);
                    leanh::lean_ctor_set(v___x_2257_, 1, v_x_2251_);
                    leanh::lean_ctor_set(v___x_2257_, 0, v_x_2252_);
                    v___x_2260_ = v___x_2257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2264_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_x_2252_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_x_2251_);
                    v___x_2260_ = v_reuseFailAlloc_2264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2261_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2254_);
                v___x_2262_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2262_, 0, v___x_2260_);
                leanh::lean_ctor_set(v___x_2262_, 1, v___x_2261_);
                v_x_2252_ = v___x_2262_;
                v_x_2253_ = v_tail_2255_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(
    mut v_x_2266_: *mut leanh::LeanObject,
    mut v_x_2267_: *mut leanh::LeanObject,
    mut v_x_2268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2273_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2268_) == 0 {
                    leanh::lean_dec(v_x_2266_);
                    return v_x_2267_;
                } else {
                    v_head_2269_ = leanh::lean_ctor_get(v_x_2268_, 0);
                    v_tail_2270_ = leanh::lean_ctor_get(v_x_2268_, 1);
                    v_isSharedCheck_2280_ = (!leanh::lean_is_exclusive(v_x_2268_)) as u8;
                    if v_isSharedCheck_2280_ == 0 {
                        v___x_2272_ = v_x_2268_;
                        v_isShared_2273_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2270_);
                        leanh::lean_inc(v_head_2269_);
                        leanh::lean_dec(v_x_2268_);
                        v___x_2272_ = leanh::lean_box(0);
                        v_isShared_2273_ = v_isSharedCheck_2280_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_2266_);
                if v_isShared_2273_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2272_, 5);
                    leanh::lean_ctor_set(v___x_2272_, 1, v_x_2266_);
                    leanh::lean_ctor_set(v___x_2272_, 0, v_x_2267_);
                    v___x_2275_ = v___x_2272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2279_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_x_2267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_x_2266_);
                    v___x_2275_ = v_reuseFailAlloc_2279_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2276_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2269_);
                v___x_2277_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2277_, 0, v___x_2275_);
                leanh::lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                v___x_2278_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(v_x_2266_, v___x_2277_, v_tail_2270_);
                return v___x_2278_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(
    mut v_x_2281_: *mut leanh::LeanObject,
    mut v_x_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2281_) == 0 {
        let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_2282_);
        v___x_2283_ = leanh::lean_box(0);
        return v___x_2283_;
    } else {
        let mut v_tail_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_2284_ = leanh::lean_ctor_get(v_x_2281_, 1);
        if leanh::lean_obj_tag(v_tail_2284_) == 0 {
            let mut v_head_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_2282_);
            v_head_2285_ = leanh::lean_ctor_get(v_x_2281_, 0);
            leanh::lean_inc(v_head_2285_);
            leanh::lean_dec_ref_known(v_x_2281_, 2);
            v___x_2286_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2285_);
            return v___x_2286_;
        } else {
            let mut v_head_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_2284_);
            v_head_2287_ = leanh::lean_ctor_get(v_x_2281_, 0);
            leanh::lean_inc(v_head_2287_);
            leanh::lean_dec_ref_known(v_x_2281_, 2);
            v___x_2288_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_2287_);
            v___x_2289_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(v_x_2282_, v___x_2288_, v_tail_2284_);
            return v___x_2289_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2295_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2;
    v___x_2296_ = lean_string_length(v___x_2295_);
    return v___x_2296_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2297_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4_once), _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4);
    v___x_2298_ = lean_nat_to_int(v___x_2297_);
    return v___x_2298_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
    mut v_a_2303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2303_) == 0 {
        let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2304_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1;
        return v___x_2304_;
    } else {
        let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2313_: u8 = 0;
        let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2305_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
        v___x_2306_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(v_a_2303_, v___x_2305_);
        v___x_2307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5_once), _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5);
        v___x_2308_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6;
        v___x_2309_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2309_, 0, v___x_2308_);
        leanh::lean_ctor_set(v___x_2309_, 1, v___x_2306_);
        v___x_2310_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7;
        v___x_2311_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2311_, 0, v___x_2309_);
        leanh::lean_ctor_set(v___x_2311_, 1, v___x_2310_);
        v___x_2312_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2312_, 0, v___x_2307_);
        leanh::lean_ctor_set(v___x_2312_, 1, v___x_2311_);
        v___x_2313_ = 0;
        v___x_2314_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_2314_, 0, v___x_2312_);
        leanh::lean_ctor_set_uint8(
            v___x_2314_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_2313_,
        );
        return v___x_2314_;
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(
    mut v_x_2315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eq_2316_: u8 = 0;
    let mut v_lhs_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eq_2316_ = leanh::lean_ctor_get_uint8(
        v_x_2315_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_lhs_2317_ = leanh::lean_ctor_get(v_x_2315_, 0);
    leanh::lean_inc(v_lhs_2317_);
    v_rhs_2318_ = leanh::lean_ctor_get(v_x_2315_, 1);
    leanh::lean_inc(v_rhs_2318_);
    leanh::lean_dec_ref(v_x_2315_);
    v___x_2319_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
    v___x_2320_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6;
    v___x_2321_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7,
    );
    v___x_2322_ = l_Bool_repr___redArg(v_eq_2316_);
    v___x_2323_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2323_, 0, v___x_2321_);
    leanh::lean_ctor_set(v___x_2323_, 1, v___x_2322_);
    v___x_2324_ = 0;
    v___x_2325_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2325_, 0, v___x_2323_);
    leanh::lean_ctor_set_uint8(
        v___x_2325_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    v___x_2326_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2326_, 0, v___x_2320_);
    leanh::lean_ctor_set(v___x_2326_, 1, v___x_2325_);
    v___x_2327_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
    v___x_2328_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2328_, 0, v___x_2326_);
    leanh::lean_ctor_set(v___x_2328_, 1, v___x_2327_);
    v___x_2329_ = leanh::lean_box(1);
    v___x_2330_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2330_, 0, v___x_2328_);
    leanh::lean_ctor_set(v___x_2330_, 1, v___x_2329_);
    v___x_2331_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11;
    v___x_2332_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2332_, 0, v___x_2330_);
    leanh::lean_ctor_set(v___x_2332_, 1, v___x_2331_);
    v___x_2333_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2333_, 0, v___x_2332_);
    leanh::lean_ctor_set(v___x_2333_, 1, v___x_2319_);
    v___x_2334_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12,
    );
    v___x_2335_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
            v_lhs_2317_,
        );
    v___x_2336_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2336_, 0, v___x_2334_);
    leanh::lean_ctor_set(v___x_2336_, 1, v___x_2335_);
    v___x_2337_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2337_, 0, v___x_2336_);
    leanh::lean_ctor_set_uint8(
        v___x_2337_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    v___x_2338_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2338_, 0, v___x_2333_);
    leanh::lean_ctor_set(v___x_2338_, 1, v___x_2337_);
    v___x_2339_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2339_, 0, v___x_2338_);
    leanh::lean_ctor_set(v___x_2339_, 1, v___x_2327_);
    v___x_2340_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2340_, 0, v___x_2339_);
    leanh::lean_ctor_set(v___x_2340_, 1, v___x_2329_);
    v___x_2341_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14;
    v___x_2342_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2342_, 0, v___x_2340_);
    leanh::lean_ctor_set(v___x_2342_, 1, v___x_2341_);
    v___x_2343_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2343_, 0, v___x_2342_);
    leanh::lean_ctor_set(v___x_2343_, 1, v___x_2319_);
    v___x_2344_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
            v_rhs_2318_,
        );
    v___x_2345_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2345_, 0, v___x_2334_);
    leanh::lean_ctor_set(v___x_2345_, 1, v___x_2344_);
    v___x_2346_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2346_, 0, v___x_2345_);
    leanh::lean_ctor_set_uint8(
        v___x_2346_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    v___x_2347_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2347_, 0, v___x_2343_);
    leanh::lean_ctor_set(v___x_2347_, 1, v___x_2346_);
    v___x_2348_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once
        ),
        _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17,
    );
    v___x_2349_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18;
    v___x_2350_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2350_, 0, v___x_2349_);
    leanh::lean_ctor_set(v___x_2350_, 1, v___x_2347_);
    v___x_2351_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19;
    v___x_2352_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2352_, 0, v___x_2350_);
    leanh::lean_ctor_set(v___x_2352_, 1, v___x_2351_);
    v___x_2353_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2353_, 0, v___x_2348_);
    leanh::lean_ctor_set(v___x_2353_, 1, v___x_2352_);
    v___x_2354_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2354_, 0, v___x_2353_);
    leanh::lean_ctor_set_uint8(
        v___x_2354_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2324_,
    );
    return v___x_2354_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(
    mut v_x_2355_: *mut leanh::LeanObject,
    mut v_prec_2356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2357_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(v_x_2355_);
    return v___x_2357_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed(
    mut v_x_2358_: *mut leanh::LeanObject,
    mut v_prec_2359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(v_x_2358_, v_prec_2359_);
    leanh::lean_dec(v_prec_2359_);
    return v_res_2360_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(
    mut v_a_2361_: *mut leanh::LeanObject,
    mut v_n_2362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2363_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(
            v_a_2361_,
        );
    return v___x_2363_;
}
pub unsafe fn l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___boxed(
    mut v_a_2364_: *mut leanh::LeanObject,
    mut v_n_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2366_ =
        l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(
            v_a_2364_, v_n_2365_,
        );
    leanh::lean_dec(v_n_2365_);
    return v_res_2366_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(
    mut v_x_2367_: *mut leanh::LeanObject,
    mut v_x_2368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_x_2367_);
    return v___x_2369_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___boxed(
    mut v_x_2370_: *mut leanh::LeanObject,
    mut v_x_2371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2372_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(v_x_2370_, v_x_2371_);
    leanh::lean_dec(v_x_2371_);
    return v_res_2372_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = leanh::lean_box(0);
    v___x_2385_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4;
    v___x_2386_ = l_Lean_mkConst(v___x_2385_, v___x_2384_);
    return v___x_2386_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = leanh::lean_box(0);
    v___x_2394_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7;
    v___x_2395_ = l_Lean_mkConst(v___x_2394_, v___x_2393_);
    return v___x_2395_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = leanh::lean_box(0);
    v___x_2403_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10;
    v___x_2404_ = l_Lean_mkConst(v___x_2403_, v___x_2402_);
    return v___x_2404_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = leanh::lean_box(0);
    v___x_2412_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13;
    v___x_2413_ = l_Lean_mkConst(v___x_2412_, v___x_2411_);
    return v___x_2413_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2420_ = leanh::lean_box(0);
    v___x_2421_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16;
    v___x_2422_ = l_Lean_mkConst(v___x_2421_, v___x_2420_);
    return v___x_2422_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(
    mut v_e_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_e_2423_) {
        0 => {
            let mut v_v_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_2424_ = leanh::lean_ctor_get(v_e_2423_, 0);
            leanh::lean_inc(v_v_2424_);
            leanh::lean_dec_ref_known(v_e_2423_, 1);
            v___x_2425_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5,
            );
            v___x_2426_ = l_Lean_mkNatLit(v_v_2424_);
            v___x_2427_ = l_Lean_Expr_app___override(v___x_2425_, v___x_2426_);
            return v___x_2427_;
        }
        1 => {
            let mut v_i_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_2428_ = leanh::lean_ctor_get(v_e_2423_, 0);
            leanh::lean_inc(v_i_2428_);
            leanh::lean_dec_ref_known(v_e_2423_, 1);
            v___x_2429_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8,
            );
            v___x_2430_ = l_Lean_mkNatLit(v_i_2428_);
            v___x_2431_ = l_Lean_Expr_app___override(v___x_2429_, v___x_2430_);
            return v___x_2431_;
        }
        2 => {
            let mut v_a_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2432_ = leanh::lean_ctor_get(v_e_2423_, 0);
            leanh::lean_inc_ref(v_a_2432_);
            v_b_2433_ = leanh::lean_ctor_get(v_e_2423_, 1);
            leanh::lean_inc_ref(v_b_2433_);
            leanh::lean_dec_ref_known(v_e_2423_, 2);
            v___x_2434_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11,
            );
            v___x_2435_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_2432_);
            v___x_2436_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_b_2433_);
            v___x_2437_ = l_Lean_mkAppB(v___x_2434_, v___x_2435_, v___x_2436_);
            return v___x_2437_;
        }
        3 => {
            let mut v_k_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_k_2438_ = leanh::lean_ctor_get(v_e_2423_, 0);
            leanh::lean_inc(v_k_2438_);
            v_a_2439_ = leanh::lean_ctor_get(v_e_2423_, 1);
            leanh::lean_inc_ref(v_a_2439_);
            leanh::lean_dec_ref_known(v_e_2423_, 2);
            v___x_2440_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14,
            );
            v___x_2441_ = l_Lean_mkNatLit(v_k_2438_);
            v___x_2442_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_2439_);
            v___x_2443_ = l_Lean_mkAppB(v___x_2440_, v___x_2441_, v___x_2442_);
            return v___x_2443_;
        }
        _ => {
            let mut v_a_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2444_ = leanh::lean_ctor_get(v_e_2423_, 0);
            leanh::lean_inc_ref(v_a_2444_);
            v_k_2445_ = leanh::lean_ctor_get(v_e_2423_, 1);
            leanh::lean_inc(v_k_2445_);
            leanh::lean_dec_ref_known(v_e_2423_, 2);
            v___x_2446_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_once
                ),
                _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17,
            );
            v___x_2447_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_2444_);
            v___x_2448_ = l_Lean_mkNatLit(v_k_2445_);
            v___x_2449_ = l_Lean_mkAppB(v___x_2446_, v___x_2447_, v___x_2448_);
            return v___x_2449_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2455_ = leanh::lean_box(0);
    v___x_2456_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1;
    v___x_2457_ = l_Lean_mkConst(v___x_2456_, v___x_2455_);
    return v___x_2457_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2458_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2,
    );
    v___f_2459_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0;
    v___x_2460_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2460_, 0, v___f_2459_);
    leanh::lean_ctor_set(v___x_2460_, 1, v___x_2458_);
    return v___x_2460_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr()
-> *mut leanh::LeanObject {
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2461_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3,
    );
    return v___x_2461_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = leanh::lean_box(0);
    v___x_2470_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2;
    v___x_2471_ = l_Lean_mkConst(v___x_2470_, v___x_2469_);
    return v___x_2471_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = leanh::lean_box(0);
    v___x_2478_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6;
    v___x_2479_ = l_Lean_mkConst(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = leanh::lean_box(0);
    v___x_2485_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9;
    v___x_2486_ = l_Lean_mkConst(v___x_2485_, v___x_2484_);
    return v___x_2486_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(
    mut v_c_2487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eq_2488_: u8 = 0;
    let mut v_lhs_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_2488_ = leanh::lean_ctor_get_uint8(
                    v_c_2487_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_2489_ = leanh::lean_ctor_get(v_c_2487_, 0);
                leanh::lean_inc_ref(v_lhs_2489_);
                v_rhs_2490_ = leanh::lean_ctor_get(v_c_2487_, 1);
                leanh::lean_inc_ref(v_rhs_2490_);
                leanh::lean_dec_ref(v_c_2487_);
                v___x_2491_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3,
                );
                if v_eq_2488_ == 0 {
                    v___x_2497_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7,
                    );
                    v___y_2493_ = v___x_2497_;
                    state = 1;
                    continue;
                } else {
                    v___x_2498_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once
                        ),
                        _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10,
                    );
                    v___y_2493_ = v___x_2498_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2494_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_lhs_2489_);
                v___x_2495_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_rhs_2490_);
                leanh::lean_inc_ref(v___y_2493_);
                v___x_2496_ = l_Lean_mkApp3(v___x_2491_, v___y_2493_, v___x_2494_, v___x_2495_);
                return v___x_2496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2504_ = leanh::lean_box(0);
    v___x_2505_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1;
    v___x_2506_ = l_Lean_mkConst(v___x_2505_, v___x_2504_);
    return v___x_2506_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2,
    );
    v___f_2508_ = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0;
    v___x_2509_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2509_, 0, v___f_2508_);
    leanh::lean_ctor_set(v___x_2509_, 1, v___x_2507_);
    return v___x_2509_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr()
-> *mut leanh::LeanObject {
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3,
    );
    return v___x_2510_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
    mut v_ctx_2511_: *mut leanh::LeanObject,
    mut v_e_2512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v_i_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2526_: u8 = 0;
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2532_: u8 = 0;
    let mut v_a_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_k_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_a_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_2512_) {
                0 => {
                    v_v_2514_ = leanh::lean_ctor_get(v_e_2512_, 0);
                    v_isSharedCheck_2522_ = (!leanh::lean_is_exclusive(v_e_2512_)) as u8;
                    if v_isSharedCheck_2522_ == 0 {
                        v___x_2516_ = v_e_2512_;
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_2514_);
                        leanh::lean_dec(v_e_2512_);
                        v___x_2516_ = leanh::lean_box(0);
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_i_2523_ = leanh::lean_ctor_get(v_e_2512_, 0);
                    v_isSharedCheck_2532_ = (!leanh::lean_is_exclusive(v_e_2512_)) as u8;
                    if v_isSharedCheck_2532_ == 0 {
                        v___x_2525_ = v_e_2512_;
                        v_isShared_2526_ = v_isSharedCheck_2532_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_2523_);
                        leanh::lean_dec(v_e_2512_);
                        v___x_2525_ = leanh::lean_box(0);
                        v_isShared_2526_ = v_isSharedCheck_2532_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_a_2533_ = leanh::lean_ctor_get(v_e_2512_, 0);
                    leanh::lean_inc_ref(v_a_2533_);
                    v_b_2534_ = leanh::lean_ctor_get(v_e_2512_, 1);
                    leanh::lean_inc_ref(v_b_2534_);
                    leanh::lean_dec_ref_known(v_e_2512_, 2);
                    v___x_2535_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_a_2533_,
                    );
                    v_a_2536_ = leanh::lean_ctor_get(v___x_2535_, 0);
                    leanh::lean_inc(v_a_2536_);
                    leanh::lean_dec_ref(v___x_2535_);
                    v___x_2537_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_b_2534_,
                    );
                    v_a_2538_ = leanh::lean_ctor_get(v___x_2537_, 0);
                    v_isSharedCheck_2546_ = (!leanh::lean_is_exclusive(v___x_2537_)) as u8;
                    if v_isSharedCheck_2546_ == 0 {
                        v___x_2540_ = v___x_2537_;
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2538_);
                        leanh::lean_dec(v___x_2537_);
                        v___x_2540_ = leanh::lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_k_2547_ = leanh::lean_ctor_get(v_e_2512_, 0);
                    leanh::lean_inc(v_k_2547_);
                    v_a_2548_ = leanh::lean_ctor_get(v_e_2512_, 1);
                    leanh::lean_inc_ref(v_a_2548_);
                    leanh::lean_dec_ref_known(v_e_2512_, 2);
                    v___x_2549_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_a_2548_,
                    );
                    v_a_2550_ = leanh::lean_ctor_get(v___x_2549_, 0);
                    v_isSharedCheck_2559_ = (!leanh::lean_is_exclusive(v___x_2549_)) as u8;
                    if v_isSharedCheck_2559_ == 0 {
                        v___x_2552_ = v___x_2549_;
                        v_isShared_2553_ = v_isSharedCheck_2559_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2550_);
                        leanh::lean_dec(v___x_2549_);
                        v___x_2552_ = leanh::lean_box(0);
                        v_isShared_2553_ = v_isSharedCheck_2559_;
                        state = 7;
                        continue;
                    }
                }
                _ => {
                    v_a_2560_ = leanh::lean_ctor_get(v_e_2512_, 0);
                    leanh::lean_inc_ref(v_a_2560_);
                    v_k_2561_ = leanh::lean_ctor_get(v_e_2512_, 1);
                    leanh::lean_inc(v_k_2561_);
                    leanh::lean_dec_ref_known(v_e_2512_, 2);
                    v___x_2562_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2511_,
                        v_a_2560_,
                    );
                    v_a_2563_ = leanh::lean_ctor_get(v___x_2562_, 0);
                    v_isSharedCheck_2572_ = (!leanh::lean_is_exclusive(v___x_2562_)) as u8;
                    if v_isSharedCheck_2572_ == 0 {
                        v___x_2565_ = v___x_2562_;
                        v_isShared_2566_ = v_isSharedCheck_2572_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2563_);
                        leanh::lean_dec(v___x_2562_);
                        v___x_2565_ = leanh::lean_box(0);
                        v_isShared_2566_ = v_isSharedCheck_2572_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2518_ = l_Lean_mkNatLit(v_v_2514_);
                if v_isShared_2517_ == 0 {
                    leanh::lean_ctor_set(v___x_2516_, 0, v___x_2518_);
                    v___x_2520_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
                    v___x_2520_ = v_reuseFailAlloc_2521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2520_;
            }
            3 => {
                v___x_2527_ = l_Lean_instInhabitedExpr;
                v___x_2528_ = lean_array_get_borrowed(v___x_2527_, v_ctx_2511_, v_i_2523_);
                leanh::lean_dec(v_i_2523_);
                leanh::lean_inc(v___x_2528_);
                if v_isShared_2526_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2525_, 0);
                    leanh::lean_ctor_set(v___x_2525_, 0, v___x_2528_);
                    v___x_2530_ = v___x_2525_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
                    v___x_2530_ = v_reuseFailAlloc_2531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2530_;
            }
            5 => {
                v___x_2542_ = l_Lean_mkNatAdd(v_a_2536_, v_a_2538_);
                if v_isShared_2541_ == 0 {
                    leanh::lean_ctor_set(v___x_2540_, 0, v___x_2542_);
                    v___x_2544_ = v___x_2540_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
                    v___x_2544_ = v_reuseFailAlloc_2545_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2544_;
            }
            7 => {
                v___x_2554_ = l_Lean_mkNatLit(v_k_2547_);
                v___x_2555_ = l_Lean_mkNatMul(v___x_2554_, v_a_2550_);
                if v_isShared_2553_ == 0 {
                    leanh::lean_ctor_set(v___x_2552_, 0, v___x_2555_);
                    v___x_2557_ = v___x_2552_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2558_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
                    v___x_2557_ = v_reuseFailAlloc_2558_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2557_;
            }
            9 => {
                v___x_2567_ = l_Lean_mkNatLit(v_k_2561_);
                v___x_2568_ = l_Lean_mkNatMul(v_a_2563_, v___x_2567_);
                if v_isShared_2566_ == 0 {
                    leanh::lean_ctor_set(v___x_2565_, 0, v___x_2568_);
                    v___x_2570_ = v___x_2565_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
                    v___x_2570_ = v_reuseFailAlloc_2571_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(
    mut v_ctx_2573_: *mut leanh::LeanObject,
    mut v_e_2574_: *mut leanh::LeanObject,
    mut v_a_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_2573_, v_e_2574_);
    leanh::lean_dec_ref(v_ctx_2573_);
    return v_res_2576_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(
    mut v_ctx_2577_: *mut leanh::LeanObject,
    mut v_e_2578_: *mut leanh::LeanObject,
    mut v_a_2579_: *mut leanh::LeanObject,
    mut v_a_2580_: *mut leanh::LeanObject,
    mut v_a_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_2577_, v_e_2578_);
    return v___x_2584_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(
    mut v_ctx_2585_: *mut leanh::LeanObject,
    mut v_e_2586_: *mut leanh::LeanObject,
    mut v_a_2587_: *mut leanh::LeanObject,
    mut v_a_2588_: *mut leanh::LeanObject,
    mut v_a_2589_: *mut leanh::LeanObject,
    mut v_a_2590_: *mut leanh::LeanObject,
    mut v_a_2591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2592_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(
        v_ctx_2585_,
        v_e_2586_,
        v_a_2587_,
        v_a_2588_,
        v_a_2589_,
        v_a_2590_,
    );
    leanh::lean_dec(v_a_2590_);
    leanh::lean_dec_ref(v_a_2589_);
    leanh::lean_dec(v_a_2588_);
    leanh::lean_dec_ref(v_a_2587_);
    leanh::lean_dec_ref(v_ctx_2585_);
    return v_res_2592_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(
    mut v_ctx_2593_: *mut leanh::LeanObject,
    mut v_c_2594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eq_2596_: u8 = 0;
    let mut v_lhs_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2610_: u8 = 0;
    let mut v_lhs_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_2596_ = leanh::lean_ctor_get_uint8(
                    v_c_2594_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_eq_2596_ == 0 {
                    v_lhs_2597_ = leanh::lean_ctor_get(v_c_2594_, 0);
                    leanh::lean_inc_ref(v_lhs_2597_);
                    v_rhs_2598_ = leanh::lean_ctor_get(v_c_2594_, 1);
                    leanh::lean_inc_ref(v_rhs_2598_);
                    leanh::lean_dec_ref(v_c_2594_);
                    v___x_2599_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_lhs_2597_,
                    );
                    v_a_2600_ = leanh::lean_ctor_get(v___x_2599_, 0);
                    leanh::lean_inc(v_a_2600_);
                    leanh::lean_dec_ref(v___x_2599_);
                    v___x_2601_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_rhs_2598_,
                    );
                    v_a_2602_ = leanh::lean_ctor_get(v___x_2601_, 0);
                    v_isSharedCheck_2610_ = (!leanh::lean_is_exclusive(v___x_2601_)) as u8;
                    if v_isSharedCheck_2610_ == 0 {
                        v___x_2604_ = v___x_2601_;
                        v_isShared_2605_ = v_isSharedCheck_2610_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2602_);
                        leanh::lean_dec(v___x_2601_);
                        v___x_2604_ = leanh::lean_box(0);
                        v_isShared_2605_ = v_isSharedCheck_2610_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_2611_ = leanh::lean_ctor_get(v_c_2594_, 0);
                    leanh::lean_inc_ref(v_lhs_2611_);
                    v_rhs_2612_ = leanh::lean_ctor_get(v_c_2594_, 1);
                    leanh::lean_inc_ref(v_rhs_2612_);
                    leanh::lean_dec_ref(v_c_2594_);
                    v___x_2613_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_lhs_2611_,
                    );
                    v_a_2614_ = leanh::lean_ctor_get(v___x_2613_, 0);
                    leanh::lean_inc(v_a_2614_);
                    leanh::lean_dec_ref(v___x_2613_);
                    v___x_2615_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                        v_ctx_2593_,
                        v_rhs_2612_,
                    );
                    v_a_2616_ = leanh::lean_ctor_get(v___x_2615_, 0);
                    v_isSharedCheck_2624_ = (!leanh::lean_is_exclusive(v___x_2615_)) as u8;
                    if v_isSharedCheck_2624_ == 0 {
                        v___x_2618_ = v___x_2615_;
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2616_);
                        leanh::lean_dec(v___x_2615_);
                        v___x_2618_ = leanh::lean_box(0);
                        v_isShared_2619_ = v_isSharedCheck_2624_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2606_ = l_Lean_mkNatLE(v_a_2600_, v_a_2602_);
                if v_isShared_2605_ == 0 {
                    leanh::lean_ctor_set(v___x_2604_, 0, v___x_2606_);
                    v___x_2608_ = v___x_2604_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2606_);
                    v___x_2608_ = v_reuseFailAlloc_2609_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2608_;
            }
            3 => {
                v___x_2620_ = l_Lean_mkNatEq(v_a_2614_, v_a_2616_);
                if v_isShared_2619_ == 0 {
                    leanh::lean_ctor_set(v___x_2618_, 0, v___x_2620_);
                    v___x_2622_ = v___x_2618_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
                    v___x_2622_ = v_reuseFailAlloc_2623_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(
    mut v_ctx_2625_: *mut leanh::LeanObject,
    mut v_c_2626_: *mut leanh::LeanObject,
    mut v_a_2627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2628_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_2625_, v_c_2626_);
    leanh::lean_dec_ref(v_ctx_2625_);
    return v_res_2628_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(
    mut v_ctx_2629_: *mut leanh::LeanObject,
    mut v_c_2630_: *mut leanh::LeanObject,
    mut v_a_2631_: *mut leanh::LeanObject,
    mut v_a_2632_: *mut leanh::LeanObject,
    mut v_a_2633_: *mut leanh::LeanObject,
    mut v_a_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_2629_, v_c_2630_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(
    mut v_ctx_2637_: *mut leanh::LeanObject,
    mut v_c_2638_: *mut leanh::LeanObject,
    mut v_a_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2644_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(
        v_ctx_2637_,
        v_c_2638_,
        v_a_2639_,
        v_a_2640_,
        v_a_2641_,
        v_a_2642_,
    );
    leanh::lean_dec(v_a_2642_);
    leanh::lean_dec_ref(v_a_2641_);
    leanh::lean_dec(v_a_2640_);
    leanh::lean_dec_ref(v_a_2639_);
    leanh::lean_dec_ref(v_ctx_2637_);
    return v_res_2644_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
    mut v_e_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
    mut v_a_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
    mut v_a_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2658_: u8 = 0;
    let mut v_val_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2677_: u8 = 0;
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2683_: u8 = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2693_: u8 = 0;
    let mut v_a_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2697_: u8 = 0;
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut v_a_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2707_: u8 = 0;
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2652_ = lean_st_ref_get(v_a_2646_);
                v_varMap_2653_ = leanh::lean_ctor_get(v___x_2652_, 0);
                leanh::lean_inc_ref(v_varMap_2653_);
                leanh::lean_dec(v___x_2652_);
                leanh::lean_inc_ref(v_e_2645_);
                v___x_2654_ = l_Lean_Meta_KExprMap_find_x3f___redArg(
                    v_varMap_2653_,
                    v_e_2645_,
                    v_a_2647_,
                    v_a_2648_,
                    v_a_2649_,
                    v_a_2650_,
                );
                leanh::lean_dec_ref(v_varMap_2653_);
                if leanh::lean_obj_tag(v___x_2654_) == 0 {
                    v_a_2655_ = leanh::lean_ctor_get(v___x_2654_, 0);
                    v_isSharedCheck_2703_ = (!leanh::lean_is_exclusive(v___x_2654_)) as u8;
                    if v_isSharedCheck_2703_ == 0 {
                        v___x_2657_ = v___x_2654_;
                        v_isShared_2658_ = v_isSharedCheck_2703_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2655_);
                        leanh::lean_dec(v___x_2654_);
                        v___x_2657_ = leanh::lean_box(0);
                        v_isShared_2658_ = v_isSharedCheck_2703_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2645_);
                    v_a_2704_ = leanh::lean_ctor_get(v___x_2654_, 0);
                    v_isSharedCheck_2711_ = (!leanh::lean_is_exclusive(v___x_2654_)) as u8;
                    if v_isSharedCheck_2711_ == 0 {
                        v___x_2706_ = v___x_2654_;
                        v_isShared_2707_ = v_isSharedCheck_2711_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2704_);
                        leanh::lean_dec(v___x_2654_);
                        v___x_2706_ = leanh::lean_box(0);
                        v_isShared_2707_ = v_isSharedCheck_2711_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2655_) == 1 {
                    leanh::lean_dec_ref(v_e_2645_);
                    v_val_2659_ = leanh::lean_ctor_get(v_a_2655_, 0);
                    v_isSharedCheck_2669_ = (!leanh::lean_is_exclusive(v_a_2655_)) as u8;
                    if v_isSharedCheck_2669_ == 0 {
                        v___x_2661_ = v_a_2655_;
                        v_isShared_2662_ = v_isSharedCheck_2669_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2659_);
                        leanh::lean_dec(v_a_2655_);
                        v___x_2661_ = leanh::lean_box(0);
                        v_isShared_2662_ = v_isSharedCheck_2669_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2657_);
                    leanh::lean_dec(v_a_2655_);
                    v___x_2670_ = lean_st_ref_get(v_a_2646_);
                    v___x_2671_ = lean_st_ref_get(v_a_2646_);
                    v_vars_2672_ = leanh::lean_ctor_get(v___x_2670_, 1);
                    leanh::lean_inc_ref(v_vars_2672_);
                    leanh::lean_dec(v___x_2670_);
                    v_varMap_2673_ = leanh::lean_ctor_get(v___x_2671_, 0);
                    v_vars_2674_ = leanh::lean_ctor_get(v___x_2671_, 1);
                    v_isSharedCheck_2702_ = (!leanh::lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2676_ = v___x_2671_;
                        v_isShared_2677_ = v_isSharedCheck_2702_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_vars_2674_);
                        leanh::lean_inc(v_varMap_2673_);
                        leanh::lean_dec(v___x_2671_);
                        v___x_2676_ = leanh::lean_box(0);
                        v_isShared_2677_ = v_isSharedCheck_2702_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2662_ == 0 {
                    v___x_2664_ = v___x_2661_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_val_2659_);
                    v___x_2664_ = v_reuseFailAlloc_2668_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2658_ == 0 {
                    leanh::lean_ctor_set(v___x_2657_, 0, v___x_2664_);
                    v___x_2666_ = v___x_2657_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
                    v___x_2666_ = v_reuseFailAlloc_2667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2666_;
            }
            5 => {
                v___x_2678_ = lean_array_get_size(v_vars_2672_);
                leanh::lean_dec_ref(v_vars_2672_);
                leanh::lean_inc_ref(v_e_2645_);
                v___x_2679_ = l_Lean_Meta_KExprMap_insert___redArg(
                    v_varMap_2673_,
                    v_e_2645_,
                    v___x_2678_,
                    v_a_2647_,
                    v_a_2648_,
                    v_a_2649_,
                    v_a_2650_,
                );
                if leanh::lean_obj_tag(v___x_2679_) == 0 {
                    v_a_2680_ = leanh::lean_ctor_get(v___x_2679_, 0);
                    v_isSharedCheck_2693_ = (!leanh::lean_is_exclusive(v___x_2679_)) as u8;
                    if v_isSharedCheck_2693_ == 0 {
                        v___x_2682_ = v___x_2679_;
                        v_isShared_2683_ = v_isSharedCheck_2693_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2680_);
                        leanh::lean_dec(v___x_2679_);
                        v___x_2682_ = leanh::lean_box(0);
                        v_isShared_2683_ = v_isSharedCheck_2693_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2676_);
                    leanh::lean_dec_ref(v_vars_2674_);
                    leanh::lean_dec_ref(v_e_2645_);
                    v_a_2694_ = leanh::lean_ctor_get(v___x_2679_, 0);
                    v_isSharedCheck_2701_ = (!leanh::lean_is_exclusive(v___x_2679_)) as u8;
                    if v_isSharedCheck_2701_ == 0 {
                        v___x_2696_ = v___x_2679_;
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2694_);
                        leanh::lean_dec(v___x_2679_);
                        v___x_2696_ = leanh::lean_box(0);
                        v_isShared_2697_ = v_isSharedCheck_2701_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2684_ = lean_array_push(v_vars_2674_, v_e_2645_);
                if v_isShared_2677_ == 0 {
                    leanh::lean_ctor_set(v___x_2676_, 1, v___x_2684_);
                    leanh::lean_ctor_set(v___x_2676_, 0, v_a_2680_);
                    v___x_2686_ = v___x_2676_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2692_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2680_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2692_, 1, v___x_2684_);
                    v___x_2686_ = v_reuseFailAlloc_2692_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2687_ = lean_st_ref_set(v_a_2646_, v___x_2686_);
                v___x_2688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2688_, 0, v___x_2678_);
                if v_isShared_2683_ == 0 {
                    leanh::lean_ctor_set(v___x_2682_, 0, v___x_2688_);
                    v___x_2690_ = v___x_2682_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2690_;
            }
            9 => {
                if v_isShared_2697_ == 0 {
                    v___x_2699_ = v___x_2696_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
                    v___x_2699_ = v_reuseFailAlloc_2700_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2699_;
            }
            11 => {
                if v_isShared_2707_ == 0 {
                    v___x_2709_ = v___x_2706_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
                    v___x_2709_ = v_reuseFailAlloc_2710_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(
    mut v_e_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v_a_2716_: *mut leanh::LeanObject,
    mut v_a_2717_: *mut leanh::LeanObject,
    mut v_a_2718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
        v_e_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_,
    );
    leanh::lean_dec(v_a_2717_);
    leanh::lean_dec_ref(v_a_2716_);
    leanh::lean_dec(v_a_2715_);
    leanh::lean_dec_ref(v_a_2714_);
    leanh::lean_dec(v_a_2713_);
    return v_res_2719_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(
    mut v_e_2757_: *mut leanh::LeanObject,
    mut v_a_2758_: *mut leanh::LeanObject,
    mut v_a_2759_: *mut leanh::LeanObject,
    mut v_a_2760_: *mut leanh::LeanObject,
    mut v_a_2761_: *mut leanh::LeanObject,
    mut v_a_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: u8 = 0;
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2773_: u8 = 0;
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_a_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_val_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut v_a_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2821_: u8 = 0;
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2825_: u8 = 0;
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: u8 = 0;
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v___x_2837_: u8 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: u8 = 0;
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u8 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u8 = 0;
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2865_: u8 = 0;
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2890_: u8 = 0;
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2901_: u8 = 0;
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_a_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2922_: u8 = 0;
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: u8 = 0;
    let mut v___x_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2952_: u8 = 0;
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2974_: u8 = 0;
    let mut v_a_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_2757_);
                v___x_2764_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2757_, v_a_2760_);
                if leanh::lean_obj_tag(v___x_2764_) == 0 {
                    v_a_2765_ = leanh::lean_ctor_get(v___x_2764_, 0);
                    leanh::lean_inc(v_a_2765_);
                    leanh::lean_dec_ref_known(v___x_2764_, 1);
                    v___x_2766_ = l_Lean_Expr_cleanupAnnotations(v_a_2765_);
                    v___x_2767_ = l_Lean_Expr_isApp(v___x_2766_);
                    if v___x_2767_ == 0 {
                        leanh::lean_dec_ref(v___x_2766_);
                        v___x_2768_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                            v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_,
                        );
                        return v___x_2768_;
                    } else {
                        v_arg_2769_ = leanh::lean_ctor_get(v___x_2766_, 1);
                        leanh::lean_inc_ref(v_arg_2769_);
                        v___x_2770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2766_);
                        v___x_2771_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1;
                        v___x_2772_ = l_Lean_Expr_isConstOf(v___x_2770_, v___x_2771_);
                        if v___x_2772_ == 0 {
                            v___x_2773_ = l_Lean_Expr_isApp(v___x_2770_);
                            if v___x_2773_ == 0 {
                                leanh::lean_dec_ref(v___x_2770_);
                                leanh::lean_dec_ref(v_arg_2769_);
                                v___x_2774_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                    v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_,
                                    v_a_2762_,
                                );
                                return v___x_2774_;
                            } else {
                                v_arg_2775_ = leanh::lean_ctor_get(v___x_2770_, 1);
                                leanh::lean_inc_ref(v_arg_2775_);
                                v___x_2826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2770_);
                                v___x_2827_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3;
                                v___x_2828_ = l_Lean_Expr_isConstOf(v___x_2826_, v___x_2827_);
                                if v___x_2828_ == 0 {
                                    v___x_2829_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4;
                                    v___x_2830_ = l_Lean_Expr_isConstOf(v___x_2826_, v___x_2829_);
                                    if v___x_2830_ == 0 {
                                        v___x_2831_ = l_Lean_Expr_isApp(v___x_2826_);
                                        if v___x_2831_ == 0 {
                                            leanh::lean_dec_ref(v___x_2826_);
                                            leanh::lean_dec_ref(v_arg_2775_);
                                            leanh::lean_dec_ref(v_arg_2769_);
                                            v___x_2832_ =
                                                l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                                    v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_,
                                                    v_a_2761_, v_a_2762_,
                                                );
                                            return v___x_2832_;
                                        } else {
                                            v_arg_2833_ =
                                                leanh::lean_ctor_get(v___x_2826_, 1);
                                            leanh::lean_inc_ref(v_arg_2833_);
                                            v___x_2834_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2826_);
                                            v___x_2835_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7;
                                            v___x_2836_ =
                                                l_Lean_Expr_isConstOf(v___x_2834_, v___x_2835_);
                                            if v___x_2836_ == 0 {
                                                v___x_2837_ = l_Lean_Expr_isApp(v___x_2834_);
                                                if v___x_2837_ == 0 {
                                                    leanh::lean_dec_ref(v___x_2834_);
                                                    leanh::lean_dec_ref(v_arg_2833_);
                                                    leanh::lean_dec_ref(v_arg_2775_);
                                                    leanh::lean_dec_ref(v_arg_2769_);
                                                    v___x_2838_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                    return v___x_2838_;
                                                } else {
                                                    v___x_2839_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_2834_,
                                                    );
                                                    v___x_2840_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9;
                                                    v___x_2841_ = l_Lean_Expr_isConstOf(
                                                        v___x_2839_,
                                                        v___x_2840_,
                                                    );
                                                    if v___x_2841_ == 0 {
                                                        v___x_2842_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11;
                                                        v___x_2843_ = l_Lean_Expr_isConstOf(
                                                            v___x_2839_,
                                                            v___x_2842_,
                                                        );
                                                        if v___x_2843_ == 0 {
                                                            v___x_2844_ =
                                                                l_Lean_Expr_isApp(v___x_2839_);
                                                            if v___x_2844_ == 0 {
                                                                leanh::lean_dec_ref(
                                                                    v___x_2839_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2833_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2775_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2769_,
                                                                );
                                                                v___x_2845_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2845_;
                                                            } else {
                                                                v___x_2846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2839_);
                                                                v___x_2847_ =
                                                                    l_Lean_Expr_isApp(v___x_2846_);
                                                                if v___x_2847_ == 0 {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_2846_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_2833_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_2775_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_2769_,
                                                                    );
                                                                    v___x_2848_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                    return v___x_2848_;
                                                                } else {
                                                                    v___x_2849_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2846_);
                                                                    v___x_2850_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14;
                                                                    v___x_2851_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_2849_,
                                                                            v___x_2850_,
                                                                        );
                                                                    if v___x_2851_ == 0 {
                                                                        v___x_2852_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17;
                                                                        v___x_2853_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_2849_,
                                                                                v___x_2852_,
                                                                            );
                                                                        leanh::lean_dec_ref(
                                                                            v___x_2849_,
                                                                        );
                                                                        if v___x_2853_ == 0 {
                                                                            leanh::lean_dec_ref(v_arg_2833_);
                                                                            leanh::lean_dec_ref(v_arg_2775_);
                                                                            leanh::lean_dec_ref(v_arg_2769_);
                                                                            v___x_2854_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                            return v___x_2854_;
                                                                        } else {
                                                                            v___x_2855_ = l_Lean_Meta_DefEq_isInstHAddNat(v_arg_2833_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                            if leanh::lean_obj_tag(v___x_2855_) == 0 {
v_a_2856_ = leanh::lean_ctor_get(v___x_2855_, 0);
leanh::lean_inc(v_a_2856_);
leanh::lean_dec_ref_known(v___x_2855_, 1);
v___x_2857_ = (leanh::lean_unbox(v_a_2856_) as u8);
leanh::lean_dec(v_a_2856_);
if v___x_2857_ == 0 {
leanh::lean_dec_ref(v_arg_2775_);
leanh::lean_dec_ref(v_arg_2769_);
v___x_2858_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
return v___x_2858_;
} else {
leanh::lean_dec_ref(v_e_2757_);
v___x_2859_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if leanh::lean_obj_tag(v___x_2859_) == 0 {
v_a_2860_ = leanh::lean_ctor_get(v___x_2859_, 0);
leanh::lean_inc(v_a_2860_);
leanh::lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2769_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if leanh::lean_obj_tag(v___x_2861_) == 0 {
v_a_2862_ = leanh::lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2870_ = (!leanh::lean_is_exclusive(v___x_2861_)) as u8;
if v_isSharedCheck_2870_ == 0 {
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2870_;
state = 10; continue;
} else {
leanh::lean_inc(v_a_2862_);
leanh::lean_dec(v___x_2861_);
v___x_2864_ = leanh::lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2870_;
state = 10; continue;
}
} else {
leanh::lean_dec(v_a_2860_);
return v___x_2861_;
}
} else {
leanh::lean_dec_ref(v_arg_2769_);
return v___x_2859_;
}
}
} else {
leanh::lean_dec_ref(v_arg_2775_);
leanh::lean_dec_ref(v_arg_2769_);
leanh::lean_dec_ref(v_e_2757_);
v_a_2871_ = leanh::lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2878_ = (!leanh::lean_is_exclusive(v___x_2855_)) as u8;
if v_isSharedCheck_2878_ == 0 {
v___x_2873_ = v___x_2855_;
v_isShared_2874_ = v_isSharedCheck_2878_;
state = 12; continue;
} else {
leanh::lean_inc(v_a_2871_);
leanh::lean_dec(v___x_2855_);
v___x_2873_ = leanh::lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
state = 12; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_2849_,
                                                                        );
                                                                        v___x_2879_ = l_Lean_Meta_DefEq_isInstHMulNat(v_arg_2833_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                        if leanh::lean_obj_tag(v___x_2879_) == 0 {
v_a_2880_ = leanh::lean_ctor_get(v___x_2879_, 0);
leanh::lean_inc(v_a_2880_);
leanh::lean_dec_ref_known(v___x_2879_, 1);
v___x_2881_ = (leanh::lean_unbox(v_a_2880_) as u8);
leanh::lean_dec(v_a_2880_);
if v___x_2881_ == 0 {
leanh::lean_dec_ref(v_arg_2775_);
leanh::lean_dec_ref(v_arg_2769_);
v___x_2882_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
return v___x_2882_;
} else {
v_b_2777_ = v_arg_2769_;
v___y_2778_ = v_a_2758_;
v___y_2779_ = v_a_2759_;
v___y_2780_ = v_a_2760_;
v___y_2781_ = v_a_2761_;
v___y_2782_ = v_a_2762_;
state = 1; continue;
}
} else {
leanh::lean_dec_ref(v_arg_2775_);
leanh::lean_dec_ref(v_arg_2769_);
leanh::lean_dec_ref(v_e_2757_);
v_a_2883_ = leanh::lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2890_ = (!leanh::lean_is_exclusive(v___x_2879_)) as u8;
if v_isSharedCheck_2890_ == 0 {
v___x_2885_ = v___x_2879_;
v_isShared_2886_ = v_isSharedCheck_2890_;
state = 14; continue;
} else {
leanh::lean_inc(v_a_2883_);
leanh::lean_dec(v___x_2879_);
v___x_2885_ = leanh::lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
state = 14; continue;
}
}
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v___x_2839_);
                                                            v___x_2891_ =
                                                                l_Lean_Meta_DefEq_isInstAddNat(
                                                                    v_arg_2833_,
                                                                    v_a_2759_,
                                                                    v_a_2760_,
                                                                    v_a_2761_,
                                                                    v_a_2762_,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v___x_2891_,
                                                            ) == 0
                                                            {
                                                                v_a_2892_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2891_,
                                                                        0,
                                                                    );
                                                                leanh::lean_inc(v_a_2892_);
                                                                leanh::lean_dec_ref_known(
                                                                    v___x_2891_,
                                                                    1,
                                                                );
                                                                v___x_2893_ =
                                                                    (leanh::lean_unbox(
                                                                        v_a_2892_,
                                                                    )
                                                                        as u8);
                                                                leanh::lean_dec(v_a_2892_);
                                                                if v___x_2893_ == 0 {
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_2775_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_2769_,
                                                                    );
                                                                    v___x_2894_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                    return v___x_2894_;
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v_e_2757_,
                                                                    );
                                                                    v___x_2895_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_2895_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_2896_ = leanh::lean_ctor_get(v___x_2895_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_2896_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_2895_, 1);
                                                                        v___x_2897_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2769_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                        if leanh::lean_obj_tag(v___x_2897_) == 0 {
v_a_2898_ = leanh::lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2906_ = (!leanh::lean_is_exclusive(v___x_2897_)) as u8;
if v_isSharedCheck_2906_ == 0 {
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2906_;
state = 16; continue;
} else {
leanh::lean_inc(v_a_2898_);
leanh::lean_dec(v___x_2897_);
v___x_2900_ = leanh::lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2906_;
state = 16; continue;
}
} else {
leanh::lean_dec(v_a_2896_);
return v___x_2897_;
}
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_2769_,
                                                                        );
                                                                        return v___x_2895_;
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2775_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2769_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_e_2757_,
                                                                );
                                                                v_a_2907_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2891_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2914_ = (!leanh::lean_is_exclusive(v___x_2891_)) as u8;
                                                                if v_isSharedCheck_2914_ == 0 {
                                                                    v___x_2909_ = v___x_2891_;
                                                                    v_isShared_2910_ =
                                                                        v_isSharedCheck_2914_;
                                                                    state = 18;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_2907_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_2891_,
                                                                    );
                                                                    v___x_2909_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_2910_ =
                                                                        v_isSharedCheck_2914_;
                                                                    state = 18;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_2839_);
                                                        v___x_2915_ =
                                                            l_Lean_Meta_DefEq_isInstMulNat(
                                                                v_arg_2833_,
                                                                v_a_2759_,
                                                                v_a_2760_,
                                                                v_a_2761_,
                                                                v_a_2762_,
                                                            );
                                                        if leanh::lean_obj_tag(v___x_2915_)
                                                            == 0
                                                        {
                                                            v_a_2916_ = leanh::lean_ctor_get(
                                                                v___x_2915_,
                                                                0,
                                                            );
                                                            leanh::lean_inc(v_a_2916_);
                                                            leanh::lean_dec_ref_known(
                                                                v___x_2915_,
                                                                1,
                                                            );
                                                            v___x_2917_ = (leanh::lean_unbox(
                                                                v_a_2916_,
                                                            )
                                                                as u8);
                                                            leanh::lean_dec(v_a_2916_);
                                                            if v___x_2917_ == 0 {
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2775_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2769_,
                                                                );
                                                                v___x_2918_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2918_;
                                                            } else {
                                                                v_b_2777_ = v_arg_2769_;
                                                                v___y_2778_ = v_a_2758_;
                                                                v___y_2779_ = v_a_2759_;
                                                                v___y_2780_ = v_a_2760_;
                                                                v___y_2781_ = v_a_2761_;
                                                                v___y_2782_ = v_a_2762_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v_arg_2775_);
                                                            leanh::lean_dec_ref(v_arg_2769_);
                                                            leanh::lean_dec_ref(v_e_2757_);
                                                            v_a_2919_ = leanh::lean_ctor_get(
                                                                v___x_2915_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2926_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_2915_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2926_ == 0 {
                                                                v___x_2921_ = v___x_2915_;
                                                                v_isShared_2922_ =
                                                                    v_isSharedCheck_2926_;
                                                                state = 20;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_2919_);
                                                                leanh::lean_dec(v___x_2915_);
                                                                v___x_2921_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_2922_ =
                                                                    v_isSharedCheck_2926_;
                                                                state = 20;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_2834_);
                                                leanh::lean_dec_ref(v_arg_2833_);
                                                leanh::lean_inc_ref(v_arg_2769_);
                                                v___x_2927_ =
                                                    l_Lean_Meta_Structural_isInstOfNatNat___redArg(
                                                        v_arg_2769_,
                                                        v_a_2760_,
                                                    );
                                                if leanh::lean_obj_tag(v___x_2927_) == 0 {
                                                    v_a_2928_ =
                                                        leanh::lean_ctor_get(v___x_2927_, 0);
                                                    leanh::lean_inc(v_a_2928_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_2927_,
                                                        1,
                                                    );
                                                    v___x_2929_ =
                                                        (leanh::lean_unbox(v_a_2928_) as u8);
                                                    leanh::lean_dec(v_a_2928_);
                                                    if v___x_2929_ == 0 {
                                                        leanh::lean_inc_ref(v_arg_2775_);
                                                        v___x_2930_ =
                                                            l_Lean_mkInstOfNatNat(v_arg_2775_);
                                                        v___x_2931_ = l_Lean_Meta_isDefEqI(
                                                            v_arg_2769_,
                                                            v___x_2930_,
                                                            v_a_2759_,
                                                            v_a_2760_,
                                                            v_a_2761_,
                                                            v_a_2762_,
                                                        );
                                                        if leanh::lean_obj_tag(v___x_2931_)
                                                            == 0
                                                        {
                                                            v_a_2932_ = leanh::lean_ctor_get(
                                                                v___x_2931_,
                                                                0,
                                                            );
                                                            leanh::lean_inc(v_a_2932_);
                                                            leanh::lean_dec_ref_known(
                                                                v___x_2931_,
                                                                1,
                                                            );
                                                            v___x_2933_ = (leanh::lean_unbox(
                                                                v_a_2932_,
                                                            )
                                                                as u8);
                                                            leanh::lean_dec(v_a_2932_);
                                                            if v___x_2933_ == 0 {
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2775_,
                                                                );
                                                                v___x_2934_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2934_;
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v_e_2757_,
                                                                );
                                                                v___x_2935_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                                return v___x_2935_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v_arg_2775_);
                                                            leanh::lean_dec_ref(v_e_2757_);
                                                            v_a_2936_ = leanh::lean_ctor_get(
                                                                v___x_2931_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_2943_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_2931_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_2943_ == 0 {
                                                                v___x_2938_ = v___x_2931_;
                                                                v_isShared_2939_ =
                                                                    v_isSharedCheck_2943_;
                                                                state = 22;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_2936_);
                                                                leanh::lean_dec(v___x_2931_);
                                                                v___x_2938_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_2939_ =
                                                                    v_isSharedCheck_2943_;
                                                                state = 22;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v_arg_2769_);
                                                        leanh::lean_dec_ref(v_e_2757_);
                                                        v___x_2944_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_2775_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
                                                        return v___x_2944_;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v_arg_2775_);
                                                    leanh::lean_dec_ref(v_arg_2769_);
                                                    leanh::lean_dec_ref(v_e_2757_);
                                                    v_a_2945_ =
                                                        leanh::lean_ctor_get(v___x_2927_, 0);
                                                    v_isSharedCheck_2952_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_2927_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2952_ == 0 {
                                                        v___x_2947_ = v___x_2927_;
                                                        v_isShared_2948_ = v_isSharedCheck_2952_;
                                                        state = 24;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_2945_);
                                                        leanh::lean_dec(v___x_2927_);
                                                        v___x_2947_ = leanh::lean_box(0);
                                                        v_isShared_2948_ = v_isSharedCheck_2952_;
                                                        state = 24;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_2826_);
                                        leanh::lean_dec_ref(v_e_2757_);
                                        v___x_2953_ =
                                            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                                v_arg_2775_,
                                                v_a_2758_,
                                                v_a_2759_,
                                                v_a_2760_,
                                                v_a_2761_,
                                                v_a_2762_,
                                            );
                                        if leanh::lean_obj_tag(v___x_2953_) == 0 {
                                            v_a_2954_ = leanh::lean_ctor_get(v___x_2953_, 0);
                                            leanh::lean_inc(v_a_2954_);
                                            leanh::lean_dec_ref_known(v___x_2953_, 1);
                                            v___x_2955_ =
                                                l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                                    v_arg_2769_,
                                                    v_a_2758_,
                                                    v_a_2759_,
                                                    v_a_2760_,
                                                    v_a_2761_,
                                                    v_a_2762_,
                                                );
                                            if leanh::lean_obj_tag(v___x_2955_) == 0 {
                                                v_a_2956_ =
                                                    leanh::lean_ctor_get(v___x_2955_, 0);
                                                v_isSharedCheck_2964_ =
                                                    (!leanh::lean_is_exclusive(v___x_2955_))
                                                        as u8;
                                                if v_isSharedCheck_2964_ == 0 {
                                                    v___x_2958_ = v___x_2955_;
                                                    v_isShared_2959_ = v_isSharedCheck_2964_;
                                                    state = 26;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_2956_);
                                                    leanh::lean_dec(v___x_2955_);
                                                    v___x_2958_ = leanh::lean_box(0);
                                                    v_isShared_2959_ = v_isSharedCheck_2964_;
                                                    state = 26;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_2954_);
                                                return v___x_2955_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_2769_);
                                            return v___x_2953_;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_2826_);
                                    v_b_2777_ = v_arg_2769_;
                                    v___y_2778_ = v_a_2758_;
                                    v___y_2779_ = v_a_2759_;
                                    v___y_2780_ = v_a_2760_;
                                    v___y_2781_ = v_a_2761_;
                                    v___y_2782_ = v_a_2762_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2770_);
                            leanh::lean_dec_ref(v_e_2757_);
                            v___x_2965_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                v_arg_2769_,
                                v_a_2758_,
                                v_a_2759_,
                                v_a_2760_,
                                v_a_2761_,
                                v_a_2762_,
                            );
                            if leanh::lean_obj_tag(v___x_2965_) == 0 {
                                v_a_2966_ = leanh::lean_ctor_get(v___x_2965_, 0);
                                v_isSharedCheck_2974_ =
                                    (!leanh::lean_is_exclusive(v___x_2965_)) as u8;
                                if v_isSharedCheck_2974_ == 0 {
                                    v___x_2968_ = v___x_2965_;
                                    v_isShared_2969_ = v_isSharedCheck_2974_;
                                    state = 28;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2966_);
                                    leanh::lean_dec(v___x_2965_);
                                    v___x_2968_ = leanh::lean_box(0);
                                    v_isShared_2969_ = v_isSharedCheck_2974_;
                                    state = 28;
                                    continue;
                                }
                            } else {
                                return v___x_2965_;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2757_);
                    v_a_2975_ = leanh::lean_ctor_get(v___x_2764_, 0);
                    v_isSharedCheck_2982_ = (!leanh::lean_is_exclusive(v___x_2764_)) as u8;
                    if v_isSharedCheck_2982_ == 0 {
                        v___x_2977_ = v___x_2764_;
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2975_);
                        leanh::lean_dec(v___x_2764_);
                        v___x_2977_ = leanh::lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 30;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_arg_2775_);
                v___x_2783_ = l_Lean_Meta_evalNat(
                    v_arg_2775_,
                    v___y_2779_,
                    v___y_2780_,
                    v___y_2781_,
                    v___y_2782_,
                );
                if leanh::lean_obj_tag(v___x_2783_) == 0 {
                    v_a_2784_ = leanh::lean_ctor_get(v___x_2783_, 0);
                    leanh::lean_inc(v_a_2784_);
                    leanh::lean_dec_ref_known(v___x_2783_, 1);
                    if leanh::lean_obj_tag(v_a_2784_) == 0 {
                        v___x_2785_ = l_Lean_Meta_evalNat(
                            v_b_2777_,
                            v___y_2779_,
                            v___y_2780_,
                            v___y_2781_,
                            v___y_2782_,
                        );
                        if leanh::lean_obj_tag(v___x_2785_) == 0 {
                            v_a_2786_ = leanh::lean_ctor_get(v___x_2785_, 0);
                            leanh::lean_inc(v_a_2786_);
                            leanh::lean_dec_ref_known(v___x_2785_, 1);
                            if leanh::lean_obj_tag(v_a_2786_) == 0 {
                                leanh::lean_dec_ref(v_arg_2775_);
                                v___x_2787_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                    v_e_2757_,
                                    v___y_2778_,
                                    v___y_2779_,
                                    v___y_2780_,
                                    v___y_2781_,
                                    v___y_2782_,
                                );
                                return v___x_2787_;
                            } else {
                                leanh::lean_dec_ref(v_e_2757_);
                                v_val_2788_ = leanh::lean_ctor_get(v_a_2786_, 0);
                                leanh::lean_inc(v_val_2788_);
                                leanh::lean_dec_ref_known(v_a_2786_, 1);
                                v___x_2789_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                    v_arg_2775_,
                                    v___y_2778_,
                                    v___y_2779_,
                                    v___y_2780_,
                                    v___y_2781_,
                                    v___y_2782_,
                                );
                                if leanh::lean_obj_tag(v___x_2789_) == 0 {
                                    v_a_2790_ = leanh::lean_ctor_get(v___x_2789_, 0);
                                    v_isSharedCheck_2798_ =
                                        (!leanh::lean_is_exclusive(v___x_2789_)) as u8;
                                    if v_isSharedCheck_2798_ == 0 {
                                        v___x_2792_ = v___x_2789_;
                                        v_isShared_2793_ = v_isSharedCheck_2798_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2790_);
                                        leanh::lean_dec(v___x_2789_);
                                        v___x_2792_ = leanh::lean_box(0);
                                        v_isShared_2793_ = v_isSharedCheck_2798_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_2788_);
                                    return v___x_2789_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_2775_);
                            leanh::lean_dec_ref(v_e_2757_);
                            v_a_2799_ = leanh::lean_ctor_get(v___x_2785_, 0);
                            v_isSharedCheck_2806_ =
                                (!leanh::lean_is_exclusive(v___x_2785_)) as u8;
                            if v_isSharedCheck_2806_ == 0 {
                                v___x_2801_ = v___x_2785_;
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2799_);
                                leanh::lean_dec(v___x_2785_);
                                v___x_2801_ = leanh::lean_box(0);
                                v_isShared_2802_ = v_isSharedCheck_2806_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_2775_);
                        leanh::lean_dec_ref(v_e_2757_);
                        v_val_2807_ = leanh::lean_ctor_get(v_a_2784_, 0);
                        leanh::lean_inc(v_val_2807_);
                        leanh::lean_dec_ref_known(v_a_2784_, 1);
                        v___x_2808_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_b_2777_,
                            v___y_2778_,
                            v___y_2779_,
                            v___y_2780_,
                            v___y_2781_,
                            v___y_2782_,
                        );
                        if leanh::lean_obj_tag(v___x_2808_) == 0 {
                            v_a_2809_ = leanh::lean_ctor_get(v___x_2808_, 0);
                            v_isSharedCheck_2817_ =
                                (!leanh::lean_is_exclusive(v___x_2808_)) as u8;
                            if v_isSharedCheck_2817_ == 0 {
                                v___x_2811_ = v___x_2808_;
                                v_isShared_2812_ = v_isSharedCheck_2817_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2809_);
                                leanh::lean_dec(v___x_2808_);
                                v___x_2811_ = leanh::lean_box(0);
                                v_isShared_2812_ = v_isSharedCheck_2817_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_2807_);
                            return v___x_2808_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_b_2777_);
                    leanh::lean_dec_ref(v_arg_2775_);
                    leanh::lean_dec_ref(v_e_2757_);
                    v_a_2818_ = leanh::lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2825_ = (!leanh::lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2825_ == 0 {
                        v___x_2820_ = v___x_2783_;
                        v_isShared_2821_ = v_isSharedCheck_2825_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2818_);
                        leanh::lean_dec(v___x_2783_);
                        v___x_2820_ = leanh::lean_box(0);
                        v_isShared_2821_ = v_isSharedCheck_2825_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2794_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2794_, 0, v_a_2790_);
                leanh::lean_ctor_set(v___x_2794_, 1, v_val_2788_);
                if v_isShared_2793_ == 0 {
                    leanh::lean_ctor_set(v___x_2792_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2792_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2796_;
            }
            4 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2804_;
            }
            6 => {
                v___x_2813_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2813_, 0, v_val_2807_);
                leanh::lean_ctor_set(v___x_2813_, 1, v_a_2809_);
                if v_isShared_2812_ == 0 {
                    leanh::lean_ctor_set(v___x_2811_, 0, v___x_2813_);
                    v___x_2815_ = v___x_2811_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2815_;
            }
            8 => {
                if v_isShared_2821_ == 0 {
                    v___x_2823_ = v___x_2820_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2824_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
                    v___x_2823_ = v_reuseFailAlloc_2824_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2823_;
            }
            10 => {
                v___x_2866_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2866_, 0, v_a_2860_);
                leanh::lean_ctor_set(v___x_2866_, 1, v_a_2862_);
                if v_isShared_2865_ == 0 {
                    leanh::lean_ctor_set(v___x_2864_, 0, v___x_2866_);
                    v___x_2868_ = v___x_2864_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2868_;
            }
            12 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2876_;
            }
            14 => {
                if v_isShared_2886_ == 0 {
                    v___x_2888_ = v___x_2885_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2889_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
                    v___x_2888_ = v_reuseFailAlloc_2889_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2888_;
            }
            16 => {
                v___x_2902_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2902_, 0, v_a_2896_);
                leanh::lean_ctor_set(v___x_2902_, 1, v_a_2898_);
                if v_isShared_2901_ == 0 {
                    leanh::lean_ctor_set(v___x_2900_, 0, v___x_2902_);
                    v___x_2904_ = v___x_2900_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
                    v___x_2904_ = v_reuseFailAlloc_2905_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2904_;
            }
            18 => {
                if v_isShared_2910_ == 0 {
                    v___x_2912_ = v___x_2909_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
                    v___x_2912_ = v_reuseFailAlloc_2913_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2912_;
            }
            20 => {
                if v_isShared_2922_ == 0 {
                    v___x_2924_ = v___x_2921_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
                    v___x_2924_ = v_reuseFailAlloc_2925_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2924_;
            }
            22 => {
                if v_isShared_2939_ == 0 {
                    v___x_2941_ = v___x_2938_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2941_;
            }
            24 => {
                if v_isShared_2948_ == 0 {
                    v___x_2950_ = v___x_2947_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
                    v___x_2950_ = v_reuseFailAlloc_2951_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2950_;
            }
            26 => {
                v___x_2960_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2960_, 0, v_a_2954_);
                leanh::lean_ctor_set(v___x_2960_, 1, v_a_2956_);
                if v_isShared_2959_ == 0 {
                    leanh::lean_ctor_set(v___x_2958_, 0, v___x_2960_);
                    v___x_2962_ = v___x_2958_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_2962_;
            }
            28 => {
                v___x_2970_ = l_Nat_Linear_Expr_inc(v_a_2966_);
                if v_isShared_2969_ == 0 {
                    leanh::lean_ctor_set(v___x_2968_, 0, v___x_2970_);
                    v___x_2972_ = v___x_2968_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
                    v___x_2972_ = v_reuseFailAlloc_2973_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2972_;
            }
            30 => {
                if v_isShared_2978_ == 0 {
                    v___x_2980_ = v___x_2977_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
    mut v_e_2983_: *mut leanh::LeanObject,
    mut v_a_2984_: *mut leanh::LeanObject,
    mut v_a_2985_: *mut leanh::LeanObject,
    mut v_a_2986_: *mut leanh::LeanObject,
    mut v_a_2987_: *mut leanh::LeanObject,
    mut v_a_2988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2999_: u8 = 0;
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_e_2983_) {
                9 => {
                    v_a_2990_ = leanh::lean_ctor_get(v_e_2983_, 0);
                    leanh::lean_inc_ref(v_a_2990_);
                    if leanh::lean_obj_tag(v_a_2990_) == 0 {
                        leanh::lean_dec_ref_known(v_e_2983_, 1);
                        v_val_2991_ = leanh::lean_ctor_get(v_a_2990_, 0);
                        v_isSharedCheck_2999_ = (!leanh::lean_is_exclusive(v_a_2990_)) as u8;
                        if v_isSharedCheck_2999_ == 0 {
                            v___x_2993_ = v_a_2990_;
                            v_isShared_2994_ = v_isSharedCheck_2999_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2991_);
                            leanh::lean_dec(v_a_2990_);
                            v___x_2993_ = leanh::lean_box(0);
                            v_isShared_2994_ = v_isSharedCheck_2999_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_2990_);
                        v___x_3000_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                            v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                        );
                        return v___x_3000_;
                    }
                }
                10 => {
                    v_expr_3001_ = leanh::lean_ctor_get(v_e_2983_, 1);
                    leanh::lean_inc_ref(v_expr_3001_);
                    leanh::lean_dec_ref_known(v_e_2983_, 2);
                    v_e_2983_ = v_expr_3001_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_declName_3003_ = leanh::lean_ctor_get(v_e_2983_, 0);
                    if leanh::lean_obj_tag(v_declName_3003_) == 1 {
                        v_pre_3004_ = leanh::lean_ctor_get(v_declName_3003_, 0);
                        if leanh::lean_obj_tag(v_pre_3004_) == 1 {
                            v_pre_3005_ = leanh::lean_ctor_get(v_pre_3004_, 0);
                            if leanh::lean_obj_tag(v_pre_3005_) == 0 {
                                v_str_3006_ = leanh::lean_ctor_get(v_declName_3003_, 1);
                                v_str_3007_ = leanh::lean_ctor_get(v_pre_3004_, 1);
                                v___x_3008_ =
                                    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
                                v___x_3009_ = lean_string_dec_eq(v_str_3007_, v___x_3008_);
                                if v___x_3009_ == 0 {
                                    v___x_3010_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                        v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                                        v_a_2988_,
                                    );
                                    return v___x_3010_;
                                } else {
                                    v___x_3011_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0;
                                    v___x_3012_ = lean_string_dec_eq(v_str_3006_, v___x_3011_);
                                    if v___x_3012_ == 0 {
                                        v___x_3013_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                            v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                                            v_a_2988_,
                                        );
                                        return v___x_3013_;
                                    } else {
                                        leanh::lean_dec_ref_known(v_e_2983_, 2);
                                        v___x_3014_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1;
                                        v___x_3015_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3015_, 0, v___x_3014_);
                                        return v___x_3015_;
                                    }
                                }
                            } else {
                                v___x_3016_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                    v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                                    v_a_2988_,
                                );
                                return v___x_3016_;
                            }
                        } else {
                            v___x_3017_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                                v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                            );
                            return v___x_3017_;
                        }
                    } else {
                        v___x_3018_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                            v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                        );
                        return v___x_3018_;
                    }
                }
                5 => {
                    v___x_3019_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
                    return v___x_3019_;
                }
                2 => {
                    v___x_3020_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
                    return v___x_3020_;
                }
                _ => {
                    v___x_3021_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(
                        v_e_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_,
                    );
                    return v___x_3021_;
                }
            },
            1 => {
                if v_isShared_2994_ == 0 {
                    v___x_2996_ = v___x_2993_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2998_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_val_2991_);
                    v___x_2996_ = v_reuseFailAlloc_2998_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2997_, 0, v___x_2996_);
                return v___x_2997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(
    mut v_e_3022_: *mut leanh::LeanObject,
    mut v_a_3023_: *mut leanh::LeanObject,
    mut v_a_3024_: *mut leanh::LeanObject,
    mut v_a_3025_: *mut leanh::LeanObject,
    mut v_a_3026_: *mut leanh::LeanObject,
    mut v_a_3027_: *mut leanh::LeanObject,
    mut v_a_3028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3029_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
        v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_,
    );
    leanh::lean_dec(v_a_3027_);
    leanh::lean_dec_ref(v_a_3026_);
    leanh::lean_dec(v_a_3025_);
    leanh::lean_dec_ref(v_a_3024_);
    leanh::lean_dec(v_a_3023_);
    return v_res_3029_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(
    mut v_e_3030_: *mut leanh::LeanObject,
    mut v_a_3031_: *mut leanh::LeanObject,
    mut v_a_3032_: *mut leanh::LeanObject,
    mut v_a_3033_: *mut leanh::LeanObject,
    mut v_a_3034_: *mut leanh::LeanObject,
    mut v_a_3035_: *mut leanh::LeanObject,
    mut v_a_3036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3037_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_);
    leanh::lean_dec(v_a_3035_);
    leanh::lean_dec_ref(v_a_3034_);
    leanh::lean_dec(v_a_3033_);
    leanh::lean_dec_ref(v_a_3032_);
    leanh::lean_dec(v_a_3031_);
    return v_res_3037_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(
    mut v_e_3069_: *mut leanh::LeanObject,
    mut v_a_3070_: *mut leanh::LeanObject,
    mut v_a_3071_: *mut leanh::LeanObject,
    mut v_a_3072_: *mut leanh::LeanObject,
    mut v_a_3073_: *mut leanh::LeanObject,
    mut v_a_3074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3080_: u8 = 0;
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v_arg_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v_arg_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v___x_3097_: u8 = 0;
    let mut v_arg_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3116_: u8 = 0;
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3128_: u8 = 0;
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_a_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v_a_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3146_: u8 = 0;
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3150_: u8 = 0;
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_a_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3155_: u8 = 0;
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3176_: u8 = 0;
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_a_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_a_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3199_: u8 = 0;
    let mut v_isSharedCheck_3200_: u8 = 0;
    let mut v_a_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3204_: u8 = 0;
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3213_: u8 = 0;
    let mut v___x_3214_: u8 = 0;
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3225_: u8 = 0;
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut v_a_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3235_: u8 = 0;
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_a_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_a_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_a_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3288_: u8 = 0;
    let mut v_a_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v_isSharedCheck_3297_: u8 = 0;
    let mut v_a_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3301_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3310_: u8 = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: u8 = 0;
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut v_a_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3334_: u8 = 0;
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3338_: u8 = 0;
    let mut v_a_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3342_: u8 = 0;
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_isSharedCheck_3347_: u8 = 0;
    let mut v_a_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3355_: u8 = 0;
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_a_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3376_: u8 = 0;
    let mut v_a_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3380_: u8 = 0;
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3391_: u8 = 0;
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3399_: u8 = 0;
    let mut v_a_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut v_a_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut v_a_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3420_: u8 = 0;
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3069_, v_a_3072_);
                if leanh::lean_obj_tag(v___x_3076_) == 0 {
                    v_a_3077_ = leanh::lean_ctor_get(v___x_3076_, 0);
                    v_isSharedCheck_3416_ = (!leanh::lean_is_exclusive(v___x_3076_)) as u8;
                    if v_isSharedCheck_3416_ == 0 {
                        v___x_3079_ = v___x_3076_;
                        v_isShared_3080_ = v_isSharedCheck_3416_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3077_);
                        leanh::lean_dec(v___x_3076_);
                        v___x_3079_ = leanh::lean_box(0);
                        v_isShared_3080_ = v_isSharedCheck_3416_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3417_ = leanh::lean_ctor_get(v___x_3076_, 0);
                    v_isSharedCheck_3424_ = (!leanh::lean_is_exclusive(v___x_3076_)) as u8;
                    if v_isSharedCheck_3424_ == 0 {
                        v___x_3419_ = v___x_3076_;
                        v_isShared_3420_ = v_isSharedCheck_3424_;
                        state = 66;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3417_);
                        leanh::lean_dec(v___x_3076_);
                        v___x_3419_ = leanh::lean_box(0);
                        v_isShared_3420_ = v_isSharedCheck_3424_;
                        state = 66;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3086_ = l_Lean_Expr_cleanupAnnotations(v_a_3077_);
                v___x_3087_ = l_Lean_Expr_isApp(v___x_3086_);
                if v___x_3087_ == 0 {
                    leanh::lean_dec_ref(v___x_3086_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3088_ = leanh::lean_ctor_get(v___x_3086_, 1);
                    leanh::lean_inc_ref(v_arg_3088_);
                    v___x_3089_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3086_);
                    v___x_3090_ = l_Lean_Expr_isApp(v___x_3089_);
                    if v___x_3090_ == 0 {
                        leanh::lean_dec_ref(v___x_3089_);
                        leanh::lean_dec_ref(v_arg_3088_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_3091_ = leanh::lean_ctor_get(v___x_3089_, 1);
                        leanh::lean_inc_ref(v_arg_3091_);
                        v___x_3092_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3089_);
                        v___x_3093_ =
                            l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1;
                        v___x_3094_ = l_Lean_Expr_isConstOf(v___x_3092_, v___x_3093_);
                        if v___x_3094_ == 0 {
                            v___x_3095_ =
                                l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3;
                            v___x_3096_ = l_Lean_Expr_isConstOf(v___x_3092_, v___x_3095_);
                            if v___x_3096_ == 0 {
                                v___x_3097_ = l_Lean_Expr_isApp(v___x_3092_);
                                if v___x_3097_ == 0 {
                                    leanh::lean_dec_ref(v___x_3092_);
                                    leanh::lean_dec_ref(v_arg_3091_);
                                    leanh::lean_dec_ref(v_arg_3088_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_3098_ = leanh::lean_ctor_get(v___x_3092_, 1);
                                    leanh::lean_inc_ref(v_arg_3098_);
                                    v___x_3099_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3092_);
                                    v___x_3100_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5;
                                    v___x_3101_ = l_Lean_Expr_isConstOf(v___x_3099_, v___x_3100_);
                                    if v___x_3101_ == 0 {
                                        v___x_3102_ = l_Lean_Expr_isApp(v___x_3099_);
                                        if v___x_3102_ == 0 {
                                            leanh::lean_dec_ref(v___x_3099_);
                                            leanh::lean_dec_ref(v_arg_3098_);
                                            leanh::lean_dec_ref(v_arg_3091_);
                                            leanh::lean_dec_ref(v_arg_3088_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_3103_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3099_);
                                            v___x_3104_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8;
                                            v___x_3105_ =
                                                l_Lean_Expr_isConstOf(v___x_3103_, v___x_3104_);
                                            if v___x_3105_ == 0 {
                                                v___x_3106_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11;
                                                v___x_3107_ =
                                                    l_Lean_Expr_isConstOf(v___x_3103_, v___x_3106_);
                                                if v___x_3107_ == 0 {
                                                    v___x_3108_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13;
                                                    v___x_3109_ = l_Lean_Expr_isConstOf(
                                                        v___x_3103_,
                                                        v___x_3108_,
                                                    );
                                                    if v___x_3109_ == 0 {
                                                        v___x_3110_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15;
                                                        v___x_3111_ = l_Lean_Expr_isConstOf(
                                                            v___x_3103_,
                                                            v___x_3110_,
                                                        );
                                                        leanh::lean_dec_ref(v___x_3103_);
                                                        if v___x_3111_ == 0 {
                                                            leanh::lean_dec_ref(v_arg_3098_);
                                                            leanh::lean_dec_ref(v_arg_3091_);
                                                            leanh::lean_dec_ref(v_arg_3088_);
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            leanh::lean_del_object(
                                                                v___x_3079_,
                                                            );
                                                            v___x_3112_ =
                                                                l_Lean_Meta_DefEq_isInstLENat(
                                                                    v_arg_3098_,
                                                                    v_a_3071_,
                                                                    v_a_3072_,
                                                                    v_a_3073_,
                                                                    v_a_3074_,
                                                                );
                                                            if leanh::lean_obj_tag(
                                                                v___x_3112_,
                                                            ) == 0
                                                            {
                                                                v_a_3113_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3112_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3151_ = (!leanh::lean_is_exclusive(v___x_3112_)) as u8;
                                                                if v_isSharedCheck_3151_ == 0 {
                                                                    v___x_3115_ = v___x_3112_;
                                                                    v_isShared_3116_ =
                                                                        v_isSharedCheck_3151_;
                                                                    state = 4;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_3113_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3112_,
                                                                    );
                                                                    v___x_3115_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_3116_ =
                                                                        v_isSharedCheck_3151_;
                                                                    state = 4;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v_arg_3091_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_3088_,
                                                                );
                                                                v_a_3152_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_3112_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_3159_ = (!leanh::lean_is_exclusive(v___x_3112_)) as u8;
                                                                if v_isSharedCheck_3159_ == 0 {
                                                                    v___x_3154_ = v___x_3112_;
                                                                    v_isShared_3155_ =
                                                                        v_isSharedCheck_3159_;
                                                                    state = 12;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_3152_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_3112_,
                                                                    );
                                                                    v___x_3154_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_3155_ =
                                                                        v_isSharedCheck_3159_;
                                                                    state = 12;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_3103_);
                                                        leanh::lean_del_object(v___x_3079_);
                                                        v___x_3160_ = l_Lean_Meta_DefEq_isInstLTNat(
                                                            v_arg_3098_,
                                                            v_a_3071_,
                                                            v_a_3072_,
                                                            v_a_3073_,
                                                            v_a_3074_,
                                                        );
                                                        if leanh::lean_obj_tag(v___x_3160_)
                                                            == 0
                                                        {
                                                            v_a_3161_ = leanh::lean_ctor_get(
                                                                v___x_3160_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3200_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_3160_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3200_ == 0 {
                                                                v___x_3163_ = v___x_3160_;
                                                                v_isShared_3164_ =
                                                                    v_isSharedCheck_3200_;
                                                                state = 14;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_3161_);
                                                                leanh::lean_dec(v___x_3160_);
                                                                v___x_3163_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_3164_ =
                                                                    v_isSharedCheck_3200_;
                                                                state = 14;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v_arg_3091_);
                                                            leanh::lean_dec_ref(v_arg_3088_);
                                                            v_a_3201_ = leanh::lean_ctor_get(
                                                                v___x_3160_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3208_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_3160_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3208_ == 0 {
                                                                v___x_3203_ = v___x_3160_;
                                                                v_isShared_3204_ =
                                                                    v_isSharedCheck_3208_;
                                                                state = 22;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_3201_);
                                                                leanh::lean_dec(v___x_3160_);
                                                                v___x_3203_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_3204_ =
                                                                    v_isSharedCheck_3208_;
                                                                state = 22;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_3103_);
                                                    leanh::lean_del_object(v___x_3079_);
                                                    v___x_3209_ = l_Lean_Meta_DefEq_isInstLENat(
                                                        v_arg_3098_,
                                                        v_a_3071_,
                                                        v_a_3072_,
                                                        v_a_3073_,
                                                        v_a_3074_,
                                                    );
                                                    if leanh::lean_obj_tag(v___x_3209_) == 0
                                                    {
                                                        v_a_3210_ = leanh::lean_ctor_get(
                                                            v___x_3209_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3248_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3209_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3248_ == 0 {
                                                            v___x_3212_ = v___x_3209_;
                                                            v_isShared_3213_ =
                                                                v_isSharedCheck_3248_;
                                                            state = 24;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3210_);
                                                            leanh::lean_dec(v___x_3209_);
                                                            v___x_3212_ = leanh::lean_box(0);
                                                            v_isShared_3213_ =
                                                                v_isSharedCheck_3248_;
                                                            state = 24;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v_arg_3091_);
                                                        leanh::lean_dec_ref(v_arg_3088_);
                                                        v_a_3249_ = leanh::lean_ctor_get(
                                                            v___x_3209_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3256_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_3209_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3256_ == 0 {
                                                            v___x_3251_ = v___x_3209_;
                                                            v_isShared_3252_ =
                                                                v_isSharedCheck_3256_;
                                                            state = 32;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_3249_);
                                                            leanh::lean_dec(v___x_3209_);
                                                            v___x_3251_ = leanh::lean_box(0);
                                                            v_isShared_3252_ =
                                                                v_isSharedCheck_3256_;
                                                            state = 32;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_3103_);
                                                leanh::lean_del_object(v___x_3079_);
                                                v___x_3257_ = l_Lean_Meta_DefEq_isInstLTNat(
                                                    v_arg_3098_,
                                                    v_a_3071_,
                                                    v_a_3072_,
                                                    v_a_3073_,
                                                    v_a_3074_,
                                                );
                                                if leanh::lean_obj_tag(v___x_3257_) == 0 {
                                                    v_a_3258_ =
                                                        leanh::lean_ctor_get(v___x_3257_, 0);
                                                    v_isSharedCheck_3297_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3257_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3297_ == 0 {
                                                        v___x_3260_ = v___x_3257_;
                                                        v_isShared_3261_ = v_isSharedCheck_3297_;
                                                        state = 34;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3258_);
                                                        leanh::lean_dec(v___x_3257_);
                                                        v___x_3260_ = leanh::lean_box(0);
                                                        v_isShared_3261_ = v_isSharedCheck_3297_;
                                                        state = 34;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v_arg_3091_);
                                                    leanh::lean_dec_ref(v_arg_3088_);
                                                    v_a_3298_ =
                                                        leanh::lean_ctor_get(v___x_3257_, 0);
                                                    v_isSharedCheck_3305_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3257_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3305_ == 0 {
                                                        v___x_3300_ = v___x_3257_;
                                                        v_isShared_3301_ = v_isSharedCheck_3305_;
                                                        state = 42;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3298_);
                                                        leanh::lean_dec(v___x_3257_);
                                                        v___x_3300_ = leanh::lean_box(0);
                                                        v_isShared_3301_ = v_isSharedCheck_3305_;
                                                        state = 42;
                                                        continue;
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_3099_);
                                        leanh::lean_del_object(v___x_3079_);
                                        v___x_3306_ =
                                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                v_arg_3098_,
                                                v_a_3072_,
                                            );
                                        if leanh::lean_obj_tag(v___x_3306_) == 0 {
                                            v_a_3307_ = leanh::lean_ctor_get(v___x_3306_, 0);
                                            v_isSharedCheck_3347_ =
                                                (!leanh::lean_is_exclusive(v___x_3306_))
                                                    as u8;
                                            if v_isSharedCheck_3347_ == 0 {
                                                v___x_3309_ = v___x_3306_;
                                                v_isShared_3310_ = v_isSharedCheck_3347_;
                                                state = 44;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3307_);
                                                leanh::lean_dec(v___x_3306_);
                                                v___x_3309_ = leanh::lean_box(0);
                                                v_isShared_3310_ = v_isSharedCheck_3347_;
                                                state = 44;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_3091_);
                                            leanh::lean_dec_ref(v_arg_3088_);
                                            v_a_3348_ = leanh::lean_ctor_get(v___x_3306_, 0);
                                            v_isSharedCheck_3355_ =
                                                (!leanh::lean_is_exclusive(v___x_3306_))
                                                    as u8;
                                            if v_isSharedCheck_3355_ == 0 {
                                                v___x_3350_ = v___x_3306_;
                                                v_isShared_3351_ = v_isSharedCheck_3355_;
                                                state = 52;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3348_);
                                                leanh::lean_dec(v___x_3306_);
                                                v___x_3350_ = leanh::lean_box(0);
                                                v_isShared_3351_ = v_isSharedCheck_3355_;
                                                state = 52;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_3092_);
                                leanh::lean_del_object(v___x_3079_);
                                v___x_3356_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                    v_arg_3091_,
                                    v_a_3070_,
                                    v_a_3071_,
                                    v_a_3072_,
                                    v_a_3073_,
                                    v_a_3074_,
                                );
                                if leanh::lean_obj_tag(v___x_3356_) == 0 {
                                    v_a_3357_ = leanh::lean_ctor_get(v___x_3356_, 0);
                                    leanh::lean_inc(v_a_3357_);
                                    leanh::lean_dec_ref_known(v___x_3356_, 1);
                                    v___x_3358_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                        v_arg_3088_,
                                        v_a_3070_,
                                        v_a_3071_,
                                        v_a_3072_,
                                        v_a_3073_,
                                        v_a_3074_,
                                    );
                                    if leanh::lean_obj_tag(v___x_3358_) == 0 {
                                        v_a_3359_ = leanh::lean_ctor_get(v___x_3358_, 0);
                                        v_isSharedCheck_3368_ =
                                            (!leanh::lean_is_exclusive(v___x_3358_)) as u8;
                                        if v_isSharedCheck_3368_ == 0 {
                                            v___x_3361_ = v___x_3358_;
                                            v_isShared_3362_ = v_isSharedCheck_3368_;
                                            state = 54;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3359_);
                                            leanh::lean_dec(v___x_3358_);
                                            v___x_3361_ = leanh::lean_box(0);
                                            v_isShared_3362_ = v_isSharedCheck_3368_;
                                            state = 54;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_3357_);
                                        v_a_3369_ = leanh::lean_ctor_get(v___x_3358_, 0);
                                        v_isSharedCheck_3376_ =
                                            (!leanh::lean_is_exclusive(v___x_3358_)) as u8;
                                        if v_isSharedCheck_3376_ == 0 {
                                            v___x_3371_ = v___x_3358_;
                                            v_isShared_3372_ = v_isSharedCheck_3376_;
                                            state = 56;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3369_);
                                            leanh::lean_dec(v___x_3358_);
                                            v___x_3371_ = leanh::lean_box(0);
                                            v_isShared_3372_ = v_isSharedCheck_3376_;
                                            state = 56;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_3088_);
                                    v_a_3377_ = leanh::lean_ctor_get(v___x_3356_, 0);
                                    v_isSharedCheck_3384_ =
                                        (!leanh::lean_is_exclusive(v___x_3356_)) as u8;
                                    if v_isSharedCheck_3384_ == 0 {
                                        v___x_3379_ = v___x_3356_;
                                        v_isShared_3380_ = v_isSharedCheck_3384_;
                                        state = 58;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3377_);
                                        leanh::lean_dec(v___x_3356_);
                                        v___x_3379_ = leanh::lean_box(0);
                                        v_isShared_3380_ = v_isSharedCheck_3384_;
                                        state = 58;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3092_);
                            leanh::lean_del_object(v___x_3079_);
                            v___x_3385_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                v_arg_3091_,
                                v_a_3070_,
                                v_a_3071_,
                                v_a_3072_,
                                v_a_3073_,
                                v_a_3074_,
                            );
                            if leanh::lean_obj_tag(v___x_3385_) == 0 {
                                v_a_3386_ = leanh::lean_ctor_get(v___x_3385_, 0);
                                leanh::lean_inc(v_a_3386_);
                                leanh::lean_dec_ref_known(v___x_3385_, 1);
                                v___x_3387_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                                    v_arg_3088_,
                                    v_a_3070_,
                                    v_a_3071_,
                                    v_a_3072_,
                                    v_a_3073_,
                                    v_a_3074_,
                                );
                                if leanh::lean_obj_tag(v___x_3387_) == 0 {
                                    v_a_3388_ = leanh::lean_ctor_get(v___x_3387_, 0);
                                    v_isSharedCheck_3399_ =
                                        (!leanh::lean_is_exclusive(v___x_3387_)) as u8;
                                    if v_isSharedCheck_3399_ == 0 {
                                        v___x_3390_ = v___x_3387_;
                                        v_isShared_3391_ = v_isSharedCheck_3399_;
                                        state = 60;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3388_);
                                        leanh::lean_dec(v___x_3387_);
                                        v___x_3390_ = leanh::lean_box(0);
                                        v_isShared_3391_ = v_isSharedCheck_3399_;
                                        state = 60;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3386_);
                                    v_a_3400_ = leanh::lean_ctor_get(v___x_3387_, 0);
                                    v_isSharedCheck_3407_ =
                                        (!leanh::lean_is_exclusive(v___x_3387_)) as u8;
                                    if v_isSharedCheck_3407_ == 0 {
                                        v___x_3402_ = v___x_3387_;
                                        v_isShared_3403_ = v_isSharedCheck_3407_;
                                        state = 62;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3400_);
                                        leanh::lean_dec(v___x_3387_);
                                        v___x_3402_ = leanh::lean_box(0);
                                        v_isShared_3403_ = v_isSharedCheck_3407_;
                                        state = 62;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_arg_3088_);
                                v_a_3408_ = leanh::lean_ctor_get(v___x_3385_, 0);
                                v_isSharedCheck_3415_ =
                                    (!leanh::lean_is_exclusive(v___x_3385_)) as u8;
                                if v_isSharedCheck_3415_ == 0 {
                                    v___x_3410_ = v___x_3385_;
                                    v_isShared_3411_ = v_isSharedCheck_3415_;
                                    state = 64;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3408_);
                                    leanh::lean_dec(v___x_3385_);
                                    v___x_3410_ = leanh::lean_box(0);
                                    v_isShared_3411_ = v_isSharedCheck_3415_;
                                    state = 64;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3082_ = leanh::lean_box(0);
                if v_isShared_3080_ == 0 {
                    leanh::lean_ctor_set(v___x_3079_, 0, v___x_3082_);
                    v___x_3084_ = v___x_3079_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
                    v___x_3084_ = v_reuseFailAlloc_3085_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3084_;
            }
            4 => {
                v___x_3117_ = (leanh::lean_unbox(v_a_3113_) as u8);
                leanh::lean_dec(v_a_3113_);
                if v___x_3117_ == 0 {
                    leanh::lean_dec_ref(v_arg_3091_);
                    leanh::lean_dec_ref(v_arg_3088_);
                    v___x_3118_ = leanh::lean_box(0);
                    if v_isShared_3116_ == 0 {
                        leanh::lean_ctor_set(v___x_3115_, 0, v___x_3118_);
                        v___x_3120_ = v___x_3115_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3121_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
                        v___x_3120_ = v_reuseFailAlloc_3121_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3115_);
                    v___x_3122_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3091_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if leanh::lean_obj_tag(v___x_3122_) == 0 {
                        v_a_3123_ = leanh::lean_ctor_get(v___x_3122_, 0);
                        leanh::lean_inc(v_a_3123_);
                        leanh::lean_dec_ref_known(v___x_3122_, 1);
                        v___x_3124_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3088_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if leanh::lean_obj_tag(v___x_3124_) == 0 {
                            v_a_3125_ = leanh::lean_ctor_get(v___x_3124_, 0);
                            v_isSharedCheck_3134_ =
                                (!leanh::lean_is_exclusive(v___x_3124_)) as u8;
                            if v_isSharedCheck_3134_ == 0 {
                                v___x_3127_ = v___x_3124_;
                                v_isShared_3128_ = v_isSharedCheck_3134_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3125_);
                                leanh::lean_dec(v___x_3124_);
                                v___x_3127_ = leanh::lean_box(0);
                                v_isShared_3128_ = v_isSharedCheck_3134_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3123_);
                            v_a_3135_ = leanh::lean_ctor_get(v___x_3124_, 0);
                            v_isSharedCheck_3142_ =
                                (!leanh::lean_is_exclusive(v___x_3124_)) as u8;
                            if v_isSharedCheck_3142_ == 0 {
                                v___x_3137_ = v___x_3124_;
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3135_);
                                leanh::lean_dec(v___x_3124_);
                                v___x_3137_ = leanh::lean_box(0);
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_3088_);
                        v_a_3143_ = leanh::lean_ctor_get(v___x_3122_, 0);
                        v_isSharedCheck_3150_ =
                            (!leanh::lean_is_exclusive(v___x_3122_)) as u8;
                        if v_isSharedCheck_3150_ == 0 {
                            v___x_3145_ = v___x_3122_;
                            v_isShared_3146_ = v_isSharedCheck_3150_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3143_);
                            leanh::lean_dec(v___x_3122_);
                            v___x_3145_ = leanh::lean_box(0);
                            v_isShared_3146_ = v_isSharedCheck_3150_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_3120_;
            }
            6 => {
                v___x_3129_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3129_, 0, v_a_3123_);
                leanh::lean_ctor_set(v___x_3129_, 1, v_a_3125_);
                leanh::lean_ctor_set_uint8(
                    v___x_3129_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3109_,
                );
                v___x_3130_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3130_, 0, v___x_3129_);
                if v_isShared_3128_ == 0 {
                    leanh::lean_ctor_set(v___x_3127_, 0, v___x_3130_);
                    v___x_3132_ = v___x_3127_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3132_;
            }
            8 => {
                if v_isShared_3138_ == 0 {
                    v___x_3140_ = v___x_3137_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
                    v___x_3140_ = v_reuseFailAlloc_3141_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3140_;
            }
            10 => {
                if v_isShared_3146_ == 0 {
                    v___x_3148_ = v___x_3145_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
                    v___x_3148_ = v_reuseFailAlloc_3149_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3148_;
            }
            12 => {
                if v_isShared_3155_ == 0 {
                    v___x_3157_ = v___x_3154_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
                    v___x_3157_ = v_reuseFailAlloc_3158_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3157_;
            }
            14 => {
                v___x_3165_ = (leanh::lean_unbox(v_a_3161_) as u8);
                leanh::lean_dec(v_a_3161_);
                if v___x_3165_ == 0 {
                    leanh::lean_dec_ref(v_arg_3091_);
                    leanh::lean_dec_ref(v_arg_3088_);
                    v___x_3166_ = leanh::lean_box(0);
                    if v_isShared_3164_ == 0 {
                        leanh::lean_ctor_set(v___x_3163_, 0, v___x_3166_);
                        v___x_3168_ = v___x_3163_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
                        v___x_3168_ = v_reuseFailAlloc_3169_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3163_);
                    v___x_3170_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3091_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if leanh::lean_obj_tag(v___x_3170_) == 0 {
                        v_a_3171_ = leanh::lean_ctor_get(v___x_3170_, 0);
                        leanh::lean_inc(v_a_3171_);
                        leanh::lean_dec_ref_known(v___x_3170_, 1);
                        v___x_3172_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3088_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if leanh::lean_obj_tag(v___x_3172_) == 0 {
                            v_a_3173_ = leanh::lean_ctor_get(v___x_3172_, 0);
                            v_isSharedCheck_3183_ =
                                (!leanh::lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3183_ == 0 {
                                v___x_3175_ = v___x_3172_;
                                v_isShared_3176_ = v_isSharedCheck_3183_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3173_);
                                leanh::lean_dec(v___x_3172_);
                                v___x_3175_ = leanh::lean_box(0);
                                v_isShared_3176_ = v_isSharedCheck_3183_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3171_);
                            v_a_3184_ = leanh::lean_ctor_get(v___x_3172_, 0);
                            v_isSharedCheck_3191_ =
                                (!leanh::lean_is_exclusive(v___x_3172_)) as u8;
                            if v_isSharedCheck_3191_ == 0 {
                                v___x_3186_ = v___x_3172_;
                                v_isShared_3187_ = v_isSharedCheck_3191_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3184_);
                                leanh::lean_dec(v___x_3172_);
                                v___x_3186_ = leanh::lean_box(0);
                                v_isShared_3187_ = v_isSharedCheck_3191_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_3088_);
                        v_a_3192_ = leanh::lean_ctor_get(v___x_3170_, 0);
                        v_isSharedCheck_3199_ =
                            (!leanh::lean_is_exclusive(v___x_3170_)) as u8;
                        if v_isSharedCheck_3199_ == 0 {
                            v___x_3194_ = v___x_3170_;
                            v_isShared_3195_ = v_isSharedCheck_3199_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3192_);
                            leanh::lean_dec(v___x_3170_);
                            v___x_3194_ = leanh::lean_box(0);
                            v_isShared_3195_ = v_isSharedCheck_3199_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            15 => {
                return v___x_3168_;
            }
            16 => {
                v___x_3177_ = l_Nat_Linear_Expr_inc(v_a_3171_);
                v___x_3178_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3178_, 0, v___x_3177_);
                leanh::lean_ctor_set(v___x_3178_, 1, v_a_3173_);
                leanh::lean_ctor_set_uint8(
                    v___x_3178_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3107_,
                );
                v___x_3179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3179_, 0, v___x_3178_);
                if v_isShared_3176_ == 0 {
                    leanh::lean_ctor_set(v___x_3175_, 0, v___x_3179_);
                    v___x_3181_ = v___x_3175_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
                    v___x_3181_ = v_reuseFailAlloc_3182_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3181_;
            }
            18 => {
                if v_isShared_3187_ == 0 {
                    v___x_3189_ = v___x_3186_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
                    v___x_3189_ = v_reuseFailAlloc_3190_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3189_;
            }
            20 => {
                if v_isShared_3195_ == 0 {
                    v___x_3197_ = v___x_3194_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
                    v___x_3197_ = v_reuseFailAlloc_3198_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3197_;
            }
            22 => {
                if v_isShared_3204_ == 0 {
                    v___x_3206_ = v___x_3203_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
                    v___x_3206_ = v_reuseFailAlloc_3207_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3206_;
            }
            24 => {
                v___x_3214_ = (leanh::lean_unbox(v_a_3210_) as u8);
                leanh::lean_dec(v_a_3210_);
                if v___x_3214_ == 0 {
                    leanh::lean_dec_ref(v_arg_3091_);
                    leanh::lean_dec_ref(v_arg_3088_);
                    v___x_3215_ = leanh::lean_box(0);
                    if v_isShared_3213_ == 0 {
                        leanh::lean_ctor_set(v___x_3212_, 0, v___x_3215_);
                        v___x_3217_ = v___x_3212_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_3218_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
                        v___x_3217_ = v_reuseFailAlloc_3218_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3212_);
                    v___x_3219_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3088_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if leanh::lean_obj_tag(v___x_3219_) == 0 {
                        v_a_3220_ = leanh::lean_ctor_get(v___x_3219_, 0);
                        leanh::lean_inc(v_a_3220_);
                        leanh::lean_dec_ref_known(v___x_3219_, 1);
                        v___x_3221_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3091_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if leanh::lean_obj_tag(v___x_3221_) == 0 {
                            v_a_3222_ = leanh::lean_ctor_get(v___x_3221_, 0);
                            v_isSharedCheck_3231_ =
                                (!leanh::lean_is_exclusive(v___x_3221_)) as u8;
                            if v_isSharedCheck_3231_ == 0 {
                                v___x_3224_ = v___x_3221_;
                                v_isShared_3225_ = v_isSharedCheck_3231_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3222_);
                                leanh::lean_dec(v___x_3221_);
                                v___x_3224_ = leanh::lean_box(0);
                                v_isShared_3225_ = v_isSharedCheck_3231_;
                                state = 26;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3220_);
                            v_a_3232_ = leanh::lean_ctor_get(v___x_3221_, 0);
                            v_isSharedCheck_3239_ =
                                (!leanh::lean_is_exclusive(v___x_3221_)) as u8;
                            if v_isSharedCheck_3239_ == 0 {
                                v___x_3234_ = v___x_3221_;
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3232_);
                                leanh::lean_dec(v___x_3221_);
                                v___x_3234_ = leanh::lean_box(0);
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_3091_);
                        v_a_3240_ = leanh::lean_ctor_get(v___x_3219_, 0);
                        v_isSharedCheck_3247_ =
                            (!leanh::lean_is_exclusive(v___x_3219_)) as u8;
                        if v_isSharedCheck_3247_ == 0 {
                            v___x_3242_ = v___x_3219_;
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3240_);
                            leanh::lean_dec(v___x_3219_);
                            v___x_3242_ = leanh::lean_box(0);
                            v_isShared_3243_ = v_isSharedCheck_3247_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            25 => {
                return v___x_3217_;
            }
            26 => {
                v___x_3226_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3226_, 0, v_a_3220_);
                leanh::lean_ctor_set(v___x_3226_, 1, v_a_3222_);
                leanh::lean_ctor_set_uint8(
                    v___x_3226_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3105_,
                );
                v___x_3227_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3227_, 0, v___x_3226_);
                if v_isShared_3225_ == 0 {
                    leanh::lean_ctor_set(v___x_3224_, 0, v___x_3227_);
                    v___x_3229_ = v___x_3224_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3230_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
                    v___x_3229_ = v_reuseFailAlloc_3230_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3229_;
            }
            28 => {
                if v_isShared_3235_ == 0 {
                    v___x_3237_ = v___x_3234_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
                    v___x_3237_ = v_reuseFailAlloc_3238_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3237_;
            }
            30 => {
                if v_isShared_3243_ == 0 {
                    v___x_3245_ = v___x_3242_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3245_;
            }
            32 => {
                if v_isShared_3252_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3255_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3254_;
            }
            34 => {
                v___x_3262_ = (leanh::lean_unbox(v_a_3258_) as u8);
                leanh::lean_dec(v_a_3258_);
                if v___x_3262_ == 0 {
                    leanh::lean_dec_ref(v_arg_3091_);
                    leanh::lean_dec_ref(v_arg_3088_);
                    v___x_3263_ = leanh::lean_box(0);
                    if v_isShared_3261_ == 0 {
                        leanh::lean_ctor_set(v___x_3260_, 0, v___x_3263_);
                        v___x_3265_ = v___x_3260_;
                        state = 35;
                        continue;
                    } else {
                        v_reuseFailAlloc_3266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3266_, 0, v___x_3263_);
                        v___x_3265_ = v_reuseFailAlloc_3266_;
                        state = 35;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3260_);
                    v___x_3267_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3088_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if leanh::lean_obj_tag(v___x_3267_) == 0 {
                        v_a_3268_ = leanh::lean_ctor_get(v___x_3267_, 0);
                        leanh::lean_inc(v_a_3268_);
                        leanh::lean_dec_ref_known(v___x_3267_, 1);
                        v___x_3269_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3091_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if leanh::lean_obj_tag(v___x_3269_) == 0 {
                            v_a_3270_ = leanh::lean_ctor_get(v___x_3269_, 0);
                            v_isSharedCheck_3280_ =
                                (!leanh::lean_is_exclusive(v___x_3269_)) as u8;
                            if v_isSharedCheck_3280_ == 0 {
                                v___x_3272_ = v___x_3269_;
                                v_isShared_3273_ = v_isSharedCheck_3280_;
                                state = 36;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3270_);
                                leanh::lean_dec(v___x_3269_);
                                v___x_3272_ = leanh::lean_box(0);
                                v_isShared_3273_ = v_isSharedCheck_3280_;
                                state = 36;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3268_);
                            v_a_3281_ = leanh::lean_ctor_get(v___x_3269_, 0);
                            v_isSharedCheck_3288_ =
                                (!leanh::lean_is_exclusive(v___x_3269_)) as u8;
                            if v_isSharedCheck_3288_ == 0 {
                                v___x_3283_ = v___x_3269_;
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 38;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3281_);
                                leanh::lean_dec(v___x_3269_);
                                v___x_3283_ = leanh::lean_box(0);
                                v_isShared_3284_ = v_isSharedCheck_3288_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_3091_);
                        v_a_3289_ = leanh::lean_ctor_get(v___x_3267_, 0);
                        v_isSharedCheck_3296_ =
                            (!leanh::lean_is_exclusive(v___x_3267_)) as u8;
                        if v_isSharedCheck_3296_ == 0 {
                            v___x_3291_ = v___x_3267_;
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 40;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3289_);
                            leanh::lean_dec(v___x_3267_);
                            v___x_3291_ = leanh::lean_box(0);
                            v_isShared_3292_ = v_isSharedCheck_3296_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            35 => {
                return v___x_3265_;
            }
            36 => {
                v___x_3274_ = l_Nat_Linear_Expr_inc(v_a_3268_);
                v___x_3275_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3275_, 0, v___x_3274_);
                leanh::lean_ctor_set(v___x_3275_, 1, v_a_3270_);
                leanh::lean_ctor_set_uint8(
                    v___x_3275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3101_,
                );
                v___x_3276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                if v_isShared_3273_ == 0 {
                    leanh::lean_ctor_set(v___x_3272_, 0, v___x_3276_);
                    v___x_3278_ = v___x_3272_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
                    v___x_3278_ = v_reuseFailAlloc_3279_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3278_;
            }
            38 => {
                if v_isShared_3284_ == 0 {
                    v___x_3286_ = v___x_3283_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3287_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
                    v___x_3286_ = v_reuseFailAlloc_3287_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3286_;
            }
            40 => {
                if v_isShared_3292_ == 0 {
                    v___x_3294_ = v___x_3291_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
                    v___x_3294_ = v_reuseFailAlloc_3295_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3294_;
            }
            42 => {
                if v_isShared_3301_ == 0 {
                    v___x_3303_ = v___x_3300_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_3304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
                    v___x_3303_ = v_reuseFailAlloc_3304_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_3303_;
            }
            44 => {
                v___x_3311_ = l_Lean_Expr_cleanupAnnotations(v_a_3307_);
                v___x_3312_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
                v___x_3313_ = l_Lean_Expr_isConstOf(v___x_3311_, v___x_3312_);
                leanh::lean_dec_ref(v___x_3311_);
                if v___x_3313_ == 0 {
                    leanh::lean_dec_ref(v_arg_3091_);
                    leanh::lean_dec_ref(v_arg_3088_);
                    v___x_3314_ = leanh::lean_box(0);
                    if v_isShared_3310_ == 0 {
                        leanh::lean_ctor_set(v___x_3309_, 0, v___x_3314_);
                        v___x_3316_ = v___x_3309_;
                        state = 45;
                        continue;
                    } else {
                        v_reuseFailAlloc_3317_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
                        v___x_3316_ = v_reuseFailAlloc_3317_;
                        state = 45;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3309_);
                    v___x_3318_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                        v_arg_3091_,
                        v_a_3070_,
                        v_a_3071_,
                        v_a_3072_,
                        v_a_3073_,
                        v_a_3074_,
                    );
                    if leanh::lean_obj_tag(v___x_3318_) == 0 {
                        v_a_3319_ = leanh::lean_ctor_get(v___x_3318_, 0);
                        leanh::lean_inc(v_a_3319_);
                        leanh::lean_dec_ref_known(v___x_3318_, 1);
                        v___x_3320_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(
                            v_arg_3088_,
                            v_a_3070_,
                            v_a_3071_,
                            v_a_3072_,
                            v_a_3073_,
                            v_a_3074_,
                        );
                        if leanh::lean_obj_tag(v___x_3320_) == 0 {
                            v_a_3321_ = leanh::lean_ctor_get(v___x_3320_, 0);
                            v_isSharedCheck_3330_ =
                                (!leanh::lean_is_exclusive(v___x_3320_)) as u8;
                            if v_isSharedCheck_3330_ == 0 {
                                v___x_3323_ = v___x_3320_;
                                v_isShared_3324_ = v_isSharedCheck_3330_;
                                state = 46;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3321_);
                                leanh::lean_dec(v___x_3320_);
                                v___x_3323_ = leanh::lean_box(0);
                                v_isShared_3324_ = v_isSharedCheck_3330_;
                                state = 46;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3319_);
                            v_a_3331_ = leanh::lean_ctor_get(v___x_3320_, 0);
                            v_isSharedCheck_3338_ =
                                (!leanh::lean_is_exclusive(v___x_3320_)) as u8;
                            if v_isSharedCheck_3338_ == 0 {
                                v___x_3333_ = v___x_3320_;
                                v_isShared_3334_ = v_isSharedCheck_3338_;
                                state = 48;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3331_);
                                leanh::lean_dec(v___x_3320_);
                                v___x_3333_ = leanh::lean_box(0);
                                v_isShared_3334_ = v_isSharedCheck_3338_;
                                state = 48;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_3088_);
                        v_a_3339_ = leanh::lean_ctor_get(v___x_3318_, 0);
                        v_isSharedCheck_3346_ =
                            (!leanh::lean_is_exclusive(v___x_3318_)) as u8;
                        if v_isSharedCheck_3346_ == 0 {
                            v___x_3341_ = v___x_3318_;
                            v_isShared_3342_ = v_isSharedCheck_3346_;
                            state = 50;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3339_);
                            leanh::lean_dec(v___x_3318_);
                            v___x_3341_ = leanh::lean_box(0);
                            v_isShared_3342_ = v_isSharedCheck_3346_;
                            state = 50;
                            continue;
                        }
                    }
                }
            }
            45 => {
                return v___x_3316_;
            }
            46 => {
                v___x_3325_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3325_, 0, v_a_3319_);
                leanh::lean_ctor_set(v___x_3325_, 1, v_a_3321_);
                leanh::lean_ctor_set_uint8(
                    v___x_3325_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3313_,
                );
                v___x_3326_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3326_, 0, v___x_3325_);
                if v_isShared_3324_ == 0 {
                    leanh::lean_ctor_set(v___x_3323_, 0, v___x_3326_);
                    v___x_3328_ = v___x_3323_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3329_, 0, v___x_3326_);
                    v___x_3328_ = v_reuseFailAlloc_3329_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3328_;
            }
            48 => {
                if v_isShared_3334_ == 0 {
                    v___x_3336_ = v___x_3333_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
                    v___x_3336_ = v_reuseFailAlloc_3337_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_3336_;
            }
            50 => {
                if v_isShared_3342_ == 0 {
                    v___x_3344_ = v___x_3341_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
                    v___x_3344_ = v_reuseFailAlloc_3345_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_3344_;
            }
            52 => {
                if v_isShared_3351_ == 0 {
                    v___x_3353_ = v___x_3350_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_3354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
                    v___x_3353_ = v_reuseFailAlloc_3354_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_3353_;
            }
            54 => {
                v___x_3363_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3363_, 0, v_a_3357_);
                leanh::lean_ctor_set(v___x_3363_, 1, v_a_3359_);
                leanh::lean_ctor_set_uint8(
                    v___x_3363_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3094_,
                );
                v___x_3364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3364_, 0, v___x_3363_);
                if v_isShared_3362_ == 0 {
                    leanh::lean_ctor_set(v___x_3361_, 0, v___x_3364_);
                    v___x_3366_ = v___x_3361_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
                    v___x_3366_ = v_reuseFailAlloc_3367_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_3366_;
            }
            56 => {
                if v_isShared_3372_ == 0 {
                    v___x_3374_ = v___x_3371_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_3375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
                    v___x_3374_ = v_reuseFailAlloc_3375_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_3374_;
            }
            58 => {
                if v_isShared_3380_ == 0 {
                    v___x_3382_ = v___x_3379_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_3382_;
            }
            60 => {
                v___x_3392_ = 0;
                v___x_3393_ = l_Nat_Linear_Expr_inc(v_a_3386_);
                v___x_3394_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3394_, 0, v___x_3393_);
                leanh::lean_ctor_set(v___x_3394_, 1, v_a_3388_);
                leanh::lean_ctor_set_uint8(
                    v___x_3394_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3392_,
                );
                v___x_3395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3395_, 0, v___x_3394_);
                if v_isShared_3391_ == 0 {
                    leanh::lean_ctor_set(v___x_3390_, 0, v___x_3395_);
                    v___x_3397_ = v___x_3390_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_3398_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
                    v___x_3397_ = v_reuseFailAlloc_3398_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_3397_;
            }
            62 => {
                if v_isShared_3403_ == 0 {
                    v___x_3405_ = v___x_3402_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_3406_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
                    v___x_3405_ = v_reuseFailAlloc_3406_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_3405_;
            }
            64 => {
                if v_isShared_3411_ == 0 {
                    v___x_3413_ = v___x_3410_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
                    v___x_3413_ = v_reuseFailAlloc_3414_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_3413_;
            }
            66 => {
                if v_isShared_3420_ == 0 {
                    v___x_3422_ = v___x_3419_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_3423_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
                    v___x_3422_ = v_reuseFailAlloc_3423_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_3422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(
    mut v_e_3425_: *mut leanh::LeanObject,
    mut v_a_3426_: *mut leanh::LeanObject,
    mut v_a_3427_: *mut leanh::LeanObject,
    mut v_a_3428_: *mut leanh::LeanObject,
    mut v_a_3429_: *mut leanh::LeanObject,
    mut v_a_3430_: *mut leanh::LeanObject,
    mut v_a_3431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(
        v_e_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_,
    );
    leanh::lean_dec(v_a_3430_);
    leanh::lean_dec_ref(v_a_3429_);
    leanh::lean_dec(v_a_3428_);
    leanh::lean_dec_ref(v_a_3427_);
    leanh::lean_dec(v_a_3426_);
    return v_res_3432_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3433_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3434_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0,
    );
    v___x_3435_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3435_, 0, v___x_3434_);
    return v___x_3435_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3438_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2;
    v___x_3439_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1,
    );
    v___x_3440_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3440_, 0, v___x_3439_);
    leanh::lean_ctor_set(v___x_3440_, 1, v___x_3438_);
    return v___x_3440_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
    mut v_x_3441_: *mut leanh::LeanObject,
    mut v_a_3442_: *mut leanh::LeanObject,
    mut v_a_3443_: *mut leanh::LeanObject,
    mut v_a_3444_: *mut leanh::LeanObject,
    mut v_a_3445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3453_: u8 = 0;
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_unused_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3467_: u8 = 0;
    let mut v_a_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3447_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3,
                );
                v___x_3448_ = lean_st_mk_ref(v___x_3447_);
                leanh::lean_inc(v_a_3445_);
                leanh::lean_inc_ref(v_a_3444_);
                leanh::lean_inc(v_a_3443_);
                leanh::lean_inc_ref(v_a_3442_);
                leanh::lean_inc(v___x_3448_);
                v___x_3449_ = leanh::lean_apply_6(
                    v_x_3441_,
                    v___x_3448_,
                    v_a_3442_,
                    v_a_3443_,
                    v_a_3444_,
                    v_a_3445_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3449_) == 0 {
                    v_a_3450_ = leanh::lean_ctor_get(v___x_3449_, 0);
                    v_isSharedCheck_3467_ = (!leanh::lean_is_exclusive(v___x_3449_)) as u8;
                    if v_isSharedCheck_3467_ == 0 {
                        v___x_3452_ = v___x_3449_;
                        v_isShared_3453_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3450_);
                        leanh::lean_dec(v___x_3449_);
                        v___x_3452_ = leanh::lean_box(0);
                        v_isShared_3453_ = v_isSharedCheck_3467_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3448_);
                    v_a_3468_ = leanh::lean_ctor_get(v___x_3449_, 0);
                    v_isSharedCheck_3475_ = (!leanh::lean_is_exclusive(v___x_3449_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v___x_3470_ = v___x_3449_;
                        v_isShared_3471_ = v_isSharedCheck_3475_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3468_);
                        leanh::lean_dec(v___x_3449_);
                        v___x_3470_ = leanh::lean_box(0);
                        v_isShared_3471_ = v_isSharedCheck_3475_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3454_ = lean_st_ref_get(v___x_3448_);
                leanh::lean_dec(v___x_3448_);
                v_vars_3455_ = leanh::lean_ctor_get(v___x_3454_, 1);
                v_isSharedCheck_3465_ = (!leanh::lean_is_exclusive(v___x_3454_)) as u8;
                if v_isSharedCheck_3465_ == 0 {
                    v_unused_3466_ = leanh::lean_ctor_get(v___x_3454_, 0);
                    leanh::lean_dec(v_unused_3466_);
                    v___x_3457_ = v___x_3454_;
                    v_isShared_3458_ = v_isSharedCheck_3465_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_vars_3455_);
                    leanh::lean_dec(v___x_3454_);
                    v___x_3457_ = leanh::lean_box(0);
                    v_isShared_3458_ = v_isSharedCheck_3465_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3458_ == 0 {
                    leanh::lean_ctor_set(v___x_3457_, 0, v_a_3450_);
                    v___x_3460_ = v___x_3457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_vars_3455_);
                    v___x_3460_ = v_reuseFailAlloc_3464_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3453_ == 0 {
                    leanh::lean_ctor_set(v___x_3452_, 0, v___x_3460_);
                    v___x_3462_ = v___x_3452_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3463_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
                    v___x_3462_ = v_reuseFailAlloc_3463_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3462_;
            }
            5 => {
                if v_isShared_3471_ == 0 {
                    v___x_3473_ = v___x_3470_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
                    v___x_3473_ = v_reuseFailAlloc_3474_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(
    mut v_x_3476_: *mut leanh::LeanObject,
    mut v_a_3477_: *mut leanh::LeanObject,
    mut v_a_3478_: *mut leanh::LeanObject,
    mut v_a_3479_: *mut leanh::LeanObject,
    mut v_a_3480_: *mut leanh::LeanObject,
    mut v_a_3481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
        v_x_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_,
    );
    leanh::lean_dec(v_a_3480_);
    leanh::lean_dec_ref(v_a_3479_);
    leanh::lean_dec(v_a_3478_);
    leanh::lean_dec_ref(v_a_3477_);
    return v_res_3482_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(
    mut v_00_u03b1_3483_: *mut leanh::LeanObject,
    mut v_x_3484_: *mut leanh::LeanObject,
    mut v_a_3485_: *mut leanh::LeanObject,
    mut v_a_3486_: *mut leanh::LeanObject,
    mut v_a_3487_: *mut leanh::LeanObject,
    mut v_a_3488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3490_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
        v_x_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_,
    );
    return v___x_3490_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(
    mut v_00_u03b1_3491_: *mut leanh::LeanObject,
    mut v_x_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
    mut v_a_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
    mut v_a_3496_: *mut leanh::LeanObject,
    mut v_a_3497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(
        v_00_u03b1_3491_,
        v_x_3492_,
        v_a_3493_,
        v_a_3494_,
        v_a_3495_,
        v_a_3496_,
    );
    leanh::lean_dec(v_a_3496_);
    leanh::lean_dec_ref(v_a_3495_);
    leanh::lean_dec(v_a_3494_);
    leanh::lean_dec_ref(v_a_3493_);
    return v_res_3498_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(
    mut v_e_3499_: *mut leanh::LeanObject,
    mut v_a_3500_: *mut leanh::LeanObject,
    mut v_a_3501_: *mut leanh::LeanObject,
    mut v_a_3502_: *mut leanh::LeanObject,
    mut v_a_3503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: u8 = 0;
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_unused_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                leanh::lean_closure_set(v___x_3505_, 0, v_e_3499_);
                v___x_3506_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
                    v___x_3505_,
                    v_a_3500_,
                    v_a_3501_,
                    v_a_3502_,
                    v_a_3503_,
                );
                if leanh::lean_obj_tag(v___x_3506_) == 0 {
                    v_a_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
                    leanh::lean_inc(v_a_3507_);
                    v_fst_3508_ = leanh::lean_ctor_get(v_a_3507_, 0);
                    leanh::lean_inc(v_fst_3508_);
                    v_snd_3509_ = leanh::lean_ctor_get(v_a_3507_, 1);
                    leanh::lean_inc(v_snd_3509_);
                    leanh::lean_dec(v_a_3507_);
                    v___x_3510_ = lean_array_get_size(v_snd_3509_);
                    v___x_3511_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3512_ = lean_nat_dec_eq(v___x_3510_, v___x_3511_);
                    if v___x_3512_ == 0 {
                        v_isSharedCheck_3531_ =
                            (!leanh::lean_is_exclusive(v___x_3506_)) as u8;
                        if v_isSharedCheck_3531_ == 0 {
                            v_unused_3532_ = leanh::lean_ctor_get(v___x_3506_, 0);
                            leanh::lean_dec(v_unused_3532_);
                            v___x_3514_ = v___x_3506_;
                            v_isShared_3515_ = v_isSharedCheck_3531_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3506_);
                            v___x_3514_ = leanh::lean_box(0);
                            v_isShared_3515_ = v_isSharedCheck_3531_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_3509_);
                        leanh::lean_dec(v_fst_3508_);
                        return v___x_3506_;
                    }
                } else {
                    return v___x_3506_;
                }
            }
            1 => {
                v___x_3516_ = 1;
                v___x_3517_ = l_Lean_sortExprs(v_snd_3509_, v___x_3516_);
                leanh::lean_dec(v_snd_3509_);
                v_fst_3518_ = leanh::lean_ctor_get(v___x_3517_, 0);
                v_snd_3519_ = leanh::lean_ctor_get(v___x_3517_, 1);
                v_isSharedCheck_3530_ = (!leanh::lean_is_exclusive(v___x_3517_)) as u8;
                if v_isSharedCheck_3530_ == 0 {
                    v___x_3521_ = v___x_3517_;
                    v_isShared_3522_ = v_isSharedCheck_3530_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3519_);
                    leanh::lean_inc(v_fst_3518_);
                    leanh::lean_dec(v___x_3517_);
                    v___x_3521_ = leanh::lean_box(0);
                    v_isShared_3522_ = v_isSharedCheck_3530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3523_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_snd_3519_, v_fst_3508_);
                leanh::lean_dec(v_snd_3519_);
                if v_isShared_3522_ == 0 {
                    leanh::lean_ctor_set(v___x_3521_, 1, v_fst_3518_);
                    leanh::lean_ctor_set(v___x_3521_, 0, v___x_3523_);
                    v___x_3525_ = v___x_3521_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3523_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 1, v_fst_3518_);
                    v___x_3525_ = v_reuseFailAlloc_3529_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3515_ == 0 {
                    leanh::lean_ctor_set(v___x_3514_, 0, v___x_3525_);
                    v___x_3527_ = v___x_3514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3527_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(
    mut v_e_3533_: *mut leanh::LeanObject,
    mut v_a_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
    mut v_a_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3539_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(
        v_e_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_,
    );
    leanh::lean_dec(v_a_3537_);
    leanh::lean_dec_ref(v_a_3536_);
    leanh::lean_dec(v_a_3535_);
    leanh::lean_dec_ref(v_a_3534_);
    return v_res_3539_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(
    mut v_e_3540_: *mut leanh::LeanObject,
    mut v_a_3541_: *mut leanh::LeanObject,
    mut v_a_3542_: *mut leanh::LeanObject,
    mut v_a_3543_: *mut leanh::LeanObject,
    mut v_a_3544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3551_: u8 = 0;
    let mut v_fst_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3556_: u8 = 0;
    let mut v_val_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3560_: u8 = 0;
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u8 = 0;
    let mut v___x_3564_: u8 = 0;
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3570_: u8 = 0;
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3591_: u8 = 0;
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut v_unused_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_a_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3602_: u8 = 0;
    let mut v___x_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3546_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                leanh::lean_closure_set(v___x_3546_, 0, v_e_3540_);
                v___x_3547_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(
                    v___x_3546_,
                    v_a_3541_,
                    v_a_3542_,
                    v_a_3543_,
                    v_a_3544_,
                );
                if leanh::lean_obj_tag(v___x_3547_) == 0 {
                    v_a_3548_ = leanh::lean_ctor_get(v___x_3547_, 0);
                    v_isSharedCheck_3598_ = (!leanh::lean_is_exclusive(v___x_3547_)) as u8;
                    if v_isSharedCheck_3598_ == 0 {
                        v___x_3550_ = v___x_3547_;
                        v_isShared_3551_ = v_isSharedCheck_3598_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3548_);
                        leanh::lean_dec(v___x_3547_);
                        v___x_3550_ = leanh::lean_box(0);
                        v_isShared_3551_ = v_isSharedCheck_3598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3599_ = leanh::lean_ctor_get(v___x_3547_, 0);
                    v_isSharedCheck_3606_ = (!leanh::lean_is_exclusive(v___x_3547_)) as u8;
                    if v_isSharedCheck_3606_ == 0 {
                        v___x_3601_ = v___x_3547_;
                        v_isShared_3602_ = v_isSharedCheck_3606_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3599_);
                        leanh::lean_dec(v___x_3547_);
                        v___x_3601_ = leanh::lean_box(0);
                        v_isShared_3602_ = v_isSharedCheck_3606_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3552_ = leanh::lean_ctor_get(v_a_3548_, 0);
                leanh::lean_inc(v_fst_3552_);
                if leanh::lean_obj_tag(v_fst_3552_) == 1 {
                    v_snd_3553_ = leanh::lean_ctor_get(v_a_3548_, 1);
                    v_isSharedCheck_3592_ = (!leanh::lean_is_exclusive(v_a_3548_)) as u8;
                    if v_isSharedCheck_3592_ == 0 {
                        v_unused_3593_ = leanh::lean_ctor_get(v_a_3548_, 0);
                        leanh::lean_dec(v_unused_3593_);
                        v___x_3555_ = v_a_3548_;
                        v_isShared_3556_ = v_isSharedCheck_3592_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3553_);
                        leanh::lean_dec(v_a_3548_);
                        v___x_3555_ = leanh::lean_box(0);
                        v_isShared_3556_ = v_isSharedCheck_3592_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_3552_);
                    leanh::lean_dec(v_a_3548_);
                    v___x_3594_ = leanh::lean_box(0);
                    if v_isShared_3551_ == 0 {
                        leanh::lean_ctor_set(v___x_3550_, 0, v___x_3594_);
                        v___x_3596_ = v___x_3550_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3597_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
                        v___x_3596_ = v_reuseFailAlloc_3597_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v_val_3557_ = leanh::lean_ctor_get(v_fst_3552_, 0);
                v_isSharedCheck_3591_ = (!leanh::lean_is_exclusive(v_fst_3552_)) as u8;
                if v_isSharedCheck_3591_ == 0 {
                    v___x_3559_ = v_fst_3552_;
                    v_isShared_3560_ = v_isSharedCheck_3591_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3557_);
                    leanh::lean_dec(v_fst_3552_);
                    v___x_3559_ = leanh::lean_box(0);
                    v_isShared_3560_ = v_isSharedCheck_3591_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3561_ = lean_array_get_size(v_snd_3553_);
                v___x_3562_ = leanh::lean_unsigned_to_nat(1);
                v___x_3563_ = lean_nat_dec_le(v___x_3561_, v___x_3562_);
                if v___x_3563_ == 0 {
                    leanh::lean_del_object(v___x_3555_);
                    v___x_3564_ = 1;
                    v___x_3565_ = l_Lean_sortExprs(v_snd_3553_, v___x_3564_);
                    leanh::lean_dec(v_snd_3553_);
                    v_fst_3566_ = leanh::lean_ctor_get(v___x_3565_, 0);
                    v_snd_3567_ = leanh::lean_ctor_get(v___x_3565_, 1);
                    v_isSharedCheck_3581_ = (!leanh::lean_is_exclusive(v___x_3565_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3569_ = v___x_3565_;
                        v_isShared_3570_ = v_isSharedCheck_3581_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3567_);
                        leanh::lean_inc(v_fst_3566_);
                        leanh::lean_dec(v___x_3565_);
                        v___x_3569_ = leanh::lean_box(0);
                        v_isShared_3570_ = v_isSharedCheck_3581_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_3556_ == 0 {
                        leanh::lean_ctor_set(v___x_3555_, 0, v_val_3557_);
                        v___x_3583_ = v___x_3555_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3590_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_val_3557_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_snd_3553_);
                        v___x_3583_ = v_reuseFailAlloc_3590_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3571_ = l_Nat_Linear_ExprCnstr_applyPerm(v_snd_3567_, v_val_3557_);
                leanh::lean_dec(v_snd_3567_);
                if v_isShared_3570_ == 0 {
                    leanh::lean_ctor_set(v___x_3569_, 1, v_fst_3566_);
                    leanh::lean_ctor_set(v___x_3569_, 0, v___x_3571_);
                    v___x_3573_ = v___x_3569_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3580_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3580_, 1, v_fst_3566_);
                    v___x_3573_ = v_reuseFailAlloc_3580_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3560_ == 0 {
                    leanh::lean_ctor_set(v___x_3559_, 0, v___x_3573_);
                    v___x_3575_ = v___x_3559_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3573_);
                    v___x_3575_ = v_reuseFailAlloc_3579_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3551_ == 0 {
                    leanh::lean_ctor_set(v___x_3550_, 0, v___x_3575_);
                    v___x_3577_ = v___x_3550_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3575_);
                    v___x_3577_ = v_reuseFailAlloc_3578_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3577_;
            }
            8 => {
                if v_isShared_3560_ == 0 {
                    leanh::lean_ctor_set(v___x_3559_, 0, v___x_3583_);
                    v___x_3585_ = v___x_3559_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3583_);
                    v___x_3585_ = v_reuseFailAlloc_3589_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3551_ == 0 {
                    leanh::lean_ctor_set(v___x_3550_, 0, v___x_3585_);
                    v___x_3587_ = v___x_3550_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3585_);
                    v___x_3587_ = v_reuseFailAlloc_3588_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3587_;
            }
            11 => {
                return v___x_3596_;
            }
            12 => {
                if v_isShared_3602_ == 0 {
                    v___x_3604_ = v___x_3601_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
                    v___x_3604_ = v_reuseFailAlloc_3605_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(
    mut v_e_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
    mut v_a_3609_: *mut leanh::LeanObject,
    mut v_a_3610_: *mut leanh::LeanObject,
    mut v_a_3611_: *mut leanh::LeanObject,
    mut v_a_3612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(
        v_e_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_,
    );
    leanh::lean_dec(v_a_3611_);
    leanh::lean_dec_ref(v_a_3610_);
    leanh::lean_dec(v_a_3609_);
    leanh::lean_dec_ref(v_a_3608_);
    return v_res_3613_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(
    mut v___y_3614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_3614_);
    return v___y_3614_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(
    mut v___y_3615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(v___y_3615_);
    leanh::lean_dec_ref(v___y_3615_);
    return v_res_3616_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3618_ = leanh::lean_box(0);
    v___x_3619_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
    v___x_3620_ = l_Lean_mkConst(v___x_3619_, v___x_3618_);
    return v___x_3620_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3621_ = leanh::lean_unsigned_to_nat(0);
    v___x_3622_ = l_Lean_mkNatLit(v___x_3621_);
    return v___x_3622_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3623_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2,
    );
    v___x_3624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3624_, 0, v___x_3623_);
    return v___x_3624_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
    mut v_ctx_3625_: *mut leanh::LeanObject,
    mut v_a_3626_: *mut leanh::LeanObject,
    mut v_a_3627_: *mut leanh::LeanObject,
    mut v_a_3628_: *mut leanh::LeanObject,
    mut v_a_3629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: u8 = 0;
    v___x_3631_ = leanh::lean_unsigned_to_nat(0);
    v___x_3632_ = lean_array_get_size(v_ctx_3625_);
    v___x_3633_ = lean_nat_dec_lt(v___x_3631_, v___x_3632_);
    if v___x_3633_ == 0 {
        let mut v___f_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ctx_3625_);
        v___f_3634_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
        v___x_3635_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once),
            _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1,
        );
        v___x_3636_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once),
            _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3,
        );
        v___x_3637_ = l_Lean_RArray_toExpr___redArg(
            v___x_3635_,
            v___f_3634_,
            v___x_3636_,
            v_a_3626_,
            v_a_3627_,
            v_a_3628_,
            v_a_3629_,
        );
        return v___x_3637_;
    } else {
        let mut v___f_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_3638_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
        v___x_3639_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once),
            _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1,
        );
        v___x_3640_ = l_Lean_RArray_ofArray___redArg(v_ctx_3625_);
        v___x_3641_ = l_Lean_RArray_toExpr___redArg(
            v___x_3639_,
            v___f_3638_,
            v___x_3640_,
            v_a_3626_,
            v_a_3627_,
            v_a_3628_,
            v_a_3629_,
        );
        return v___x_3641_;
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(
    mut v_ctx_3642_: *mut leanh::LeanObject,
    mut v_a_3643_: *mut leanh::LeanObject,
    mut v_a_3644_: *mut leanh::LeanObject,
    mut v_a_3645_: *mut leanh::LeanObject,
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v_a_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3648_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
        v_ctx_3642_,
        v_a_3643_,
        v_a_3644_,
        v_a_3645_,
        v_a_3646_,
    );
    leanh::lean_dec(v_a_3646_);
    leanh::lean_dec_ref(v_a_3645_);
    leanh::lean_dec(v_a_3644_);
    leanh::lean_dec_ref(v_a_3643_);
    return v_res_3648_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_SortExprs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_KExprMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr =
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr();
    leanh::lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr);
    l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr =
        _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr();
    leanh::lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_SortExprs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_KExprMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_RArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_NatInstTesters(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
}