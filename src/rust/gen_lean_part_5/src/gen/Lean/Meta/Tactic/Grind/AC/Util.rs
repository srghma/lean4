// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Util
// Imports: Lean.Meta.Tactic.Grind.AC.Types Lean.Meta.Tactic.Grind.ProveEq Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Simp
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_array_uset,
    lean_grind_internalize, lean_infer_type, lean_instantiate_expr_mvars, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isApp, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Types::{
    initialize_Lean_Meta_Tactic_Grind_AC_Types, l_Lean_Meta_Grind_AC_acExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingId::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
    l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f,
    l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::ProveEq::{
    initialize_Lean_Meta_Tactic_Grind_ProveEq, runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_preprocessLight___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_getState___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_getConfig___redArg,
    l_Lean_Meta_Grind_getGeneration___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value: leanh::LeanStringObject<
    45,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 115, 116, 114, 117, 99, 116,
        117, 114, 101, 32, 105, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_instMonadGetStructACM_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_AC_ACM_getStruct___boxed as *const core::ffi::c_void,
        m_arity: 12,
        m_num_fixed: 0,
        m_objs: [],
    };
pub static mut l_Lean_Meta_Grind_AC_instMonadGetStructACM: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instMonadGetStructACM_value)
        as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__2_value) as *mut leanh::LeanObject,9743492140944907313 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__4_value) as *mut leanh::LeanObject,14181099489592536354 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__6_value) as *mut leanh::LeanObject,9917798623386220051 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [71, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [103, 101, 116, 69, 108, 101, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__8_value) as *mut leanh::LeanObject,854136310249810287 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__9_value) as *mut leanh::LeanObject,8801718159307809986 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__11_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__12_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__14_value) as *mut leanh::LeanObject,18356704233129443855 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__16_value) as *mut leanh::LeanObject,8391571994004792969 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__18_value) as *mut leanh::LeanObject,105488867511536770 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 84, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__20_value) as *mut leanh::LeanObject,17878876274162330439 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__21_value) as *mut leanh::LeanObject,11833570877100518198 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [76, 69, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__23_value) as *mut leanh::LeanObject,8347582161988589016 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__24_value) as *mut leanh::LeanObject,7316284823769321069 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__25_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__22_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__26_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__19_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__27_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__17_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__28_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__15_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__29_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__13_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__30_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__10_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__31_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__32_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__33_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__34_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__35_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__0_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__1_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__3_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__4_value) as *mut leanh::LeanObject,1611444129324655608 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__6_value) as *mut leanh::LeanObject,16856108565602861689 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__7_value) as *mut leanh::LeanObject,4187025665268973031 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__9_value) as *mut leanh::LeanObject,11858238400308895562 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__10_value) as *mut leanh::LeanObject,6100819061652633370 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__12_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__13_value) as *mut leanh::LeanObject,10422657989269798688 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [44, 32, 110, 101, 117, 116, 114, 97, 108, 63, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [60, 110, 111, 116, 45, 97, 118, 97, 105, 108, 97, 98, 108, 101, 62, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [44, 32, 105, 100, 101, 109, 112, 111, 116, 101, 110, 116, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [97, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__9_value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__10_value) as *mut leanh::LeanObject,5637236024813792860 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__11_value) as *mut leanh::LeanObject,13988555943647875614 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__12_value) as *mut leanh::LeanObject,15368431810600006387 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__14_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 32, 99, 111, 109, 109, 58, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [65, 115, 115, 111, 99, 105, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__20_value) as *mut leanh::LeanObject,17561379004628073218 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 109, 109, 117, 116, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__22_value) as *mut leanh::LeanObject,234445833000607850 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [73, 100, 101, 109, 112, 111, 116, 101, 110, 116, 79, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__24_value) as *mut leanh::LeanObject,16442335306435255285 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [76, 97, 119, 102, 117, 108, 73, 100, 101, 110, 116, 105, 116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__19_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__26_value) as *mut leanh::LeanObject,18153903751919310386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27___redArg(
    mut v_a_2488_: *mut leanh::LeanObject,
    mut v_a_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2492_ =
        l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_2491_, v_a_2488_, v_a_2489_);
    return v___x_2492_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27___redArg___boxed(
    mut v_a_2493_: *mut leanh::LeanObject,
    mut v_a_2494_: *mut leanh::LeanObject,
    mut v_a_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2496_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2493_, v_a_2494_);
    leanh::lean_dec_ref(v_a_2494_);
    leanh::lean_dec(v_a_2493_);
    return v_res_2496_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27(
    mut v_a_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
    mut v_a_2501_: *mut leanh::LeanObject,
    mut v_a_2502_: *mut leanh::LeanObject,
    mut v_a_2503_: *mut leanh::LeanObject,
    mut v_a_2504_: *mut leanh::LeanObject,
    mut v_a_2505_: *mut leanh::LeanObject,
    mut v_a_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2497_, v_a_2505_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_get_x27___boxed(
    mut v_a_2509_: *mut leanh::LeanObject,
    mut v_a_2510_: *mut leanh::LeanObject,
    mut v_a_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
    mut v_a_2515_: *mut leanh::LeanObject,
    mut v_a_2516_: *mut leanh::LeanObject,
    mut v_a_2517_: *mut leanh::LeanObject,
    mut v_a_2518_: *mut leanh::LeanObject,
    mut v_a_2519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2520_ = l_Lean_Meta_Grind_AC_get_x27(
        v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_,
        v_a_2517_, v_a_2518_,
    );
    leanh::lean_dec(v_a_2518_);
    leanh::lean_dec_ref(v_a_2517_);
    leanh::lean_dec(v_a_2516_);
    leanh::lean_dec_ref(v_a_2515_);
    leanh::lean_dec(v_a_2514_);
    leanh::lean_dec_ref(v_a_2513_);
    leanh::lean_dec(v_a_2512_);
    leanh::lean_dec_ref(v_a_2511_);
    leanh::lean_dec(v_a_2510_);
    leanh::lean_dec(v_a_2509_);
    return v_res_2520_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27___redArg(
    mut v_f_2521_: *mut leanh::LeanObject,
    mut v_a_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2525_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2524_, v_f_2521_, v_a_2522_);
    return v___x_2525_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27___redArg___boxed(
    mut v_f_2526_: *mut leanh::LeanObject,
    mut v_a_2527_: *mut leanh::LeanObject,
    mut v_a_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Lean_Meta_Grind_AC_modify_x27___redArg(v_f_2526_, v_a_2527_);
    leanh::lean_dec(v_a_2527_);
    return v_res_2529_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27(
    mut v_f_2530_: *mut leanh::LeanObject,
    mut v_a_2531_: *mut leanh::LeanObject,
    mut v_a_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
    mut v_a_2534_: *mut leanh::LeanObject,
    mut v_a_2535_: *mut leanh::LeanObject,
    mut v_a_2536_: *mut leanh::LeanObject,
    mut v_a_2537_: *mut leanh::LeanObject,
    mut v_a_2538_: *mut leanh::LeanObject,
    mut v_a_2539_: *mut leanh::LeanObject,
    mut v_a_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2542_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2543_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2542_, v_f_2530_, v_a_2531_);
    return v___x_2543_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modify_x27___boxed(
    mut v_f_2544_: *mut leanh::LeanObject,
    mut v_a_2545_: *mut leanh::LeanObject,
    mut v_a_2546_: *mut leanh::LeanObject,
    mut v_a_2547_: *mut leanh::LeanObject,
    mut v_a_2548_: *mut leanh::LeanObject,
    mut v_a_2549_: *mut leanh::LeanObject,
    mut v_a_2550_: *mut leanh::LeanObject,
    mut v_a_2551_: *mut leanh::LeanObject,
    mut v_a_2552_: *mut leanh::LeanObject,
    mut v_a_2553_: *mut leanh::LeanObject,
    mut v_a_2554_: *mut leanh::LeanObject,
    mut v_a_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Lean_Meta_Grind_AC_modify_x27(
        v_f_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_,
        v_a_2552_, v_a_2553_, v_a_2554_,
    );
    leanh::lean_dec(v_a_2554_);
    leanh::lean_dec_ref(v_a_2553_);
    leanh::lean_dec(v_a_2552_);
    leanh::lean_dec_ref(v_a_2551_);
    leanh::lean_dec(v_a_2550_);
    leanh::lean_dec_ref(v_a_2549_);
    leanh::lean_dec(v_a_2548_);
    leanh::lean_dec_ref(v_a_2547_);
    leanh::lean_dec(v_a_2546_);
    leanh::lean_dec(v_a_2545_);
    return v_res_2556_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(
    mut v_a_2557_: *mut leanh::LeanObject,
    mut v_a_2558_: *mut leanh::LeanObject,
    mut v_a_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v_acSteps_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v_a_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2583_: u8 = 0;
    let mut v_a_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2587_: u8 = 0;
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2561_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2557_, v_a_2559_);
                if leanh::lean_obj_tag(v___x_2561_) == 0 {
                    v_a_2562_ = leanh::lean_ctor_get(v___x_2561_, 0);
                    leanh::lean_inc(v_a_2562_);
                    leanh::lean_dec_ref_known(v___x_2561_, 1);
                    v___x_2563_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2558_);
                    if leanh::lean_obj_tag(v___x_2563_) == 0 {
                        v_a_2564_ = leanh::lean_ctor_get(v___x_2563_, 0);
                        v_isSharedCheck_2575_ =
                            (!leanh::lean_is_exclusive(v___x_2563_)) as u8;
                        if v_isSharedCheck_2575_ == 0 {
                            v___x_2566_ = v___x_2563_;
                            v_isShared_2567_ = v_isSharedCheck_2575_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2564_);
                            leanh::lean_dec(v___x_2563_);
                            v___x_2566_ = leanh::lean_box(0);
                            v_isShared_2567_ = v_isSharedCheck_2575_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2562_);
                        v_a_2576_ = leanh::lean_ctor_get(v___x_2563_, 0);
                        v_isSharedCheck_2583_ =
                            (!leanh::lean_is_exclusive(v___x_2563_)) as u8;
                        if v_isSharedCheck_2583_ == 0 {
                            v___x_2578_ = v___x_2563_;
                            v_isShared_2579_ = v_isSharedCheck_2583_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2576_);
                            leanh::lean_dec(v___x_2563_);
                            v___x_2578_ = leanh::lean_box(0);
                            v_isShared_2579_ = v_isSharedCheck_2583_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2584_ = leanh::lean_ctor_get(v___x_2561_, 0);
                    v_isSharedCheck_2591_ = (!leanh::lean_is_exclusive(v___x_2561_)) as u8;
                    if v_isSharedCheck_2591_ == 0 {
                        v___x_2586_ = v___x_2561_;
                        v_isShared_2587_ = v_isSharedCheck_2591_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2584_);
                        leanh::lean_dec(v___x_2561_);
                        v___x_2586_ = leanh::lean_box(0);
                        v_isShared_2587_ = v_isSharedCheck_2591_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_acSteps_2568_ = leanh::lean_ctor_get(v_a_2564_, 8);
                leanh::lean_inc(v_acSteps_2568_);
                leanh::lean_dec(v_a_2564_);
                v_steps_2569_ = leanh::lean_ctor_get(v_a_2562_, 3);
                leanh::lean_inc(v_steps_2569_);
                leanh::lean_dec(v_a_2562_);
                v___x_2570_ = lean_nat_dec_le(v_acSteps_2568_, v_steps_2569_);
                leanh::lean_dec(v_steps_2569_);
                leanh::lean_dec(v_acSteps_2568_);
                v___x_2571_ = leanh::lean_box((v___x_2570_) as usize);
                if v_isShared_2567_ == 0 {
                    leanh::lean_ctor_set(v___x_2566_, 0, v___x_2571_);
                    v___x_2573_ = v___x_2566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
                    v___x_2573_ = v_reuseFailAlloc_2574_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2573_;
            }
            3 => {
                if v_isShared_2579_ == 0 {
                    v___x_2581_ = v___x_2578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2582_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
                    v___x_2581_ = v_reuseFailAlloc_2582_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2581_;
            }
            5 => {
                if v_isShared_2587_ == 0 {
                    v___x_2589_ = v___x_2586_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
                    v___x_2589_ = v_reuseFailAlloc_2590_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps___redArg___boxed(
    mut v_a_2592_: *mut leanh::LeanObject,
    mut v_a_2593_: *mut leanh::LeanObject,
    mut v_a_2594_: *mut leanh::LeanObject,
    mut v_a_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_2592_, v_a_2593_, v_a_2594_);
    leanh::lean_dec_ref(v_a_2594_);
    leanh::lean_dec_ref(v_a_2593_);
    leanh::lean_dec(v_a_2592_);
    return v_res_2596_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps(
    mut v_a_2597_: *mut leanh::LeanObject,
    mut v_a_2598_: *mut leanh::LeanObject,
    mut v_a_2599_: *mut leanh::LeanObject,
    mut v_a_2600_: *mut leanh::LeanObject,
    mut v_a_2601_: *mut leanh::LeanObject,
    mut v_a_2602_: *mut leanh::LeanObject,
    mut v_a_2603_: *mut leanh::LeanObject,
    mut v_a_2604_: *mut leanh::LeanObject,
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_a_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2608_ = l_Lean_Meta_Grind_AC_checkMaxSteps___redArg(v_a_2597_, v_a_2599_, v_a_2605_);
    return v___x_2608_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_checkMaxSteps___boxed(
    mut v_a_2609_: *mut leanh::LeanObject,
    mut v_a_2610_: *mut leanh::LeanObject,
    mut v_a_2611_: *mut leanh::LeanObject,
    mut v_a_2612_: *mut leanh::LeanObject,
    mut v_a_2613_: *mut leanh::LeanObject,
    mut v_a_2614_: *mut leanh::LeanObject,
    mut v_a_2615_: *mut leanh::LeanObject,
    mut v_a_2616_: *mut leanh::LeanObject,
    mut v_a_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2620_ = l_Lean_Meta_Grind_AC_checkMaxSteps(
        v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_,
        v_a_2617_, v_a_2618_,
    );
    leanh::lean_dec(v_a_2618_);
    leanh::lean_dec_ref(v_a_2617_);
    leanh::lean_dec(v_a_2616_);
    leanh::lean_dec_ref(v_a_2615_);
    leanh::lean_dec(v_a_2614_);
    leanh::lean_dec_ref(v_a_2613_);
    leanh::lean_dec(v_a_2612_);
    leanh::lean_dec_ref(v_a_2611_);
    leanh::lean_dec(v_a_2610_);
    leanh::lean_dec(v_a_2609_);
    return v_res_2620_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___redArg___lam__0(
    mut v_s_2621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2628_: u8 = 0;
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2622_ = leanh::lean_ctor_get(v_s_2621_, 0);
                v_opIdOf_2623_ = leanh::lean_ctor_get(v_s_2621_, 1);
                v_exprToOpIds_2624_ = leanh::lean_ctor_get(v_s_2621_, 2);
                v_steps_2625_ = leanh::lean_ctor_get(v_s_2621_, 3);
                v_isSharedCheck_2634_ = (!leanh::lean_is_exclusive(v_s_2621_)) as u8;
                if v_isSharedCheck_2634_ == 0 {
                    v___x_2627_ = v_s_2621_;
                    v_isShared_2628_ = v_isSharedCheck_2634_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_2625_);
                    leanh::lean_inc(v_exprToOpIds_2624_);
                    leanh::lean_inc(v_opIdOf_2623_);
                    leanh::lean_inc(v_structs_2622_);
                    leanh::lean_dec(v_s_2621_);
                    v___x_2627_ = leanh::lean_box(0);
                    v_isShared_2628_ = v_isSharedCheck_2634_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2629_ = leanh::lean_unsigned_to_nat(1);
                v___x_2630_ = lean_nat_add(v_steps_2625_, v___x_2629_);
                leanh::lean_dec(v_steps_2625_);
                if v_isShared_2628_ == 0 {
                    leanh::lean_ctor_set(v___x_2627_, 3, v___x_2630_);
                    v___x_2632_ = v___x_2627_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2633_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_structs_2622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_opIdOf_2623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 2, v_exprToOpIds_2624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2633_, 3, v___x_2630_);
                    v___x_2632_ = v_reuseFailAlloc_2633_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___redArg(
    mut v_a_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2638_ = l_Lean_Meta_Grind_AC_incSteps___redArg___closed__0;
    v___x_2639_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2640_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2639_, v___f_2638_, v_a_2636_);
    return v___x_2640_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___redArg___boxed(
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2643_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_2641_);
    leanh::lean_dec(v_a_2641_);
    return v_res_2643_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps(
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
    mut v_a_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
    mut v_a_2650_: *mut leanh::LeanObject,
    mut v_a_2651_: *mut leanh::LeanObject,
    mut v_a_2652_: *mut leanh::LeanObject,
    mut v_a_2653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = l_Lean_Meta_Grind_AC_incSteps___redArg(v_a_2644_);
    return v___x_2655_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_incSteps___boxed(
    mut v_a_2656_: *mut leanh::LeanObject,
    mut v_a_2657_: *mut leanh::LeanObject,
    mut v_a_2658_: *mut leanh::LeanObject,
    mut v_a_2659_: *mut leanh::LeanObject,
    mut v_a_2660_: *mut leanh::LeanObject,
    mut v_a_2661_: *mut leanh::LeanObject,
    mut v_a_2662_: *mut leanh::LeanObject,
    mut v_a_2663_: *mut leanh::LeanObject,
    mut v_a_2664_: *mut leanh::LeanObject,
    mut v_a_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2667_ = l_Lean_Meta_Grind_AC_incSteps(
        v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_,
        v_a_2664_, v_a_2665_,
    );
    leanh::lean_dec(v_a_2665_);
    leanh::lean_dec_ref(v_a_2664_);
    leanh::lean_dec(v_a_2663_);
    leanh::lean_dec_ref(v_a_2662_);
    leanh::lean_dec(v_a_2661_);
    leanh::lean_dec_ref(v_a_2660_);
    leanh::lean_dec(v_a_2659_);
    leanh::lean_dec_ref(v_a_2658_);
    leanh::lean_dec(v_a_2657_);
    leanh::lean_dec(v_a_2656_);
    return v_res_2667_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift___redArg(
    mut v_inst_2668_: *mut leanh::LeanObject,
    mut v_inst_2669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2670_ = leanh::lean_apply_2(v_inst_2668_, leanh::lean_box(0), v_inst_2669_);
    return v___x_2670_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_instMonadGetStructOfMonadLift(
    mut v_m_2671_: *mut leanh::LeanObject,
    mut v_n_2672_: *mut leanh::LeanObject,
    mut v_inst_2673_: *mut leanh::LeanObject,
    mut v_inst_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = leanh::lean_apply_2(v_inst_2673_, leanh::lean_box(0), v_inst_2674_);
    return v___x_2675_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run___redArg(
    mut v_opId_2676_: *mut leanh::LeanObject,
    mut v_x_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
    mut v_a_2679_: *mut leanh::LeanObject,
    mut v_a_2680_: *mut leanh::LeanObject,
    mut v_a_2681_: *mut leanh::LeanObject,
    mut v_a_2682_: *mut leanh::LeanObject,
    mut v_a_2683_: *mut leanh::LeanObject,
    mut v_a_2684_: *mut leanh::LeanObject,
    mut v_a_2685_: *mut leanh::LeanObject,
    mut v_a_2686_: *mut leanh::LeanObject,
    mut v_a_2687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2687_);
    leanh::lean_inc_ref(v_a_2686_);
    leanh::lean_inc(v_a_2685_);
    leanh::lean_inc_ref(v_a_2684_);
    leanh::lean_inc(v_a_2683_);
    leanh::lean_inc_ref(v_a_2682_);
    leanh::lean_inc(v_a_2681_);
    leanh::lean_inc_ref(v_a_2680_);
    leanh::lean_inc(v_a_2679_);
    leanh::lean_inc(v_a_2678_);
    v___x_2689_ = leanh::lean_apply_12(
        v_x_2677_,
        v_opId_2676_,
        v_a_2678_,
        v_a_2679_,
        v_a_2680_,
        v_a_2681_,
        v_a_2682_,
        v_a_2683_,
        v_a_2684_,
        v_a_2685_,
        v_a_2686_,
        v_a_2687_,
        leanh::lean_box(0),
    );
    return v___x_2689_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run___redArg___boxed(
    mut v_opId_2690_: *mut leanh::LeanObject,
    mut v_x_2691_: *mut leanh::LeanObject,
    mut v_a_2692_: *mut leanh::LeanObject,
    mut v_a_2693_: *mut leanh::LeanObject,
    mut v_a_2694_: *mut leanh::LeanObject,
    mut v_a_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
    mut v_a_2698_: *mut leanh::LeanObject,
    mut v_a_2699_: *mut leanh::LeanObject,
    mut v_a_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2703_ = l_Lean_Meta_Grind_AC_ACM_run___redArg(
        v_opId_2690_,
        v_x_2691_,
        v_a_2692_,
        v_a_2693_,
        v_a_2694_,
        v_a_2695_,
        v_a_2696_,
        v_a_2697_,
        v_a_2698_,
        v_a_2699_,
        v_a_2700_,
        v_a_2701_,
    );
    leanh::lean_dec(v_a_2701_);
    leanh::lean_dec_ref(v_a_2700_);
    leanh::lean_dec(v_a_2699_);
    leanh::lean_dec_ref(v_a_2698_);
    leanh::lean_dec(v_a_2697_);
    leanh::lean_dec_ref(v_a_2696_);
    leanh::lean_dec(v_a_2695_);
    leanh::lean_dec_ref(v_a_2694_);
    leanh::lean_dec(v_a_2693_);
    leanh::lean_dec(v_a_2692_);
    return v_res_2703_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run(
    mut v_00_u03b1_2704_: *mut leanh::LeanObject,
    mut v_opId_2705_: *mut leanh::LeanObject,
    mut v_x_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
    mut v_a_2708_: *mut leanh::LeanObject,
    mut v_a_2709_: *mut leanh::LeanObject,
    mut v_a_2710_: *mut leanh::LeanObject,
    mut v_a_2711_: *mut leanh::LeanObject,
    mut v_a_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v_a_2716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2716_);
    leanh::lean_inc_ref(v_a_2715_);
    leanh::lean_inc(v_a_2714_);
    leanh::lean_inc_ref(v_a_2713_);
    leanh::lean_inc(v_a_2712_);
    leanh::lean_inc_ref(v_a_2711_);
    leanh::lean_inc(v_a_2710_);
    leanh::lean_inc_ref(v_a_2709_);
    leanh::lean_inc(v_a_2708_);
    leanh::lean_inc(v_a_2707_);
    v___x_2718_ = leanh::lean_apply_12(
        v_x_2706_,
        v_opId_2705_,
        v_a_2707_,
        v_a_2708_,
        v_a_2709_,
        v_a_2710_,
        v_a_2711_,
        v_a_2712_,
        v_a_2713_,
        v_a_2714_,
        v_a_2715_,
        v_a_2716_,
        leanh::lean_box(0),
    );
    return v___x_2718_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_run___boxed(
    mut v_00_u03b1_2719_: *mut leanh::LeanObject,
    mut v_opId_2720_: *mut leanh::LeanObject,
    mut v_x_2721_: *mut leanh::LeanObject,
    mut v_a_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
    mut v_a_2724_: *mut leanh::LeanObject,
    mut v_a_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_a_2732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2733_ = l_Lean_Meta_Grind_AC_ACM_run(
        v_00_u03b1_2719_,
        v_opId_2720_,
        v_x_2721_,
        v_a_2722_,
        v_a_2723_,
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
        v_a_2727_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        v_a_2731_,
    );
    leanh::lean_dec(v_a_2731_);
    leanh::lean_dec_ref(v_a_2730_);
    leanh::lean_dec(v_a_2729_);
    leanh::lean_dec_ref(v_a_2728_);
    leanh::lean_dec(v_a_2727_);
    leanh::lean_dec_ref(v_a_2726_);
    leanh::lean_dec(v_a_2725_);
    leanh::lean_dec_ref(v_a_2724_);
    leanh::lean_dec(v_a_2723_);
    leanh::lean_dec(v_a_2722_);
    return v_res_2733_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId___redArg(
    mut v_a_2734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2734_);
    v___x_2736_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2736_, 0, v_a_2734_);
    return v___x_2736_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId___redArg___boxed(
    mut v_a_2737_: *mut leanh::LeanObject,
    mut v_a_2738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Lean_Meta_Grind_AC_getOpId___redArg(v_a_2737_);
    leanh::lean_dec(v_a_2737_);
    return v_res_2739_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId(
    mut v_a_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
    mut v_a_2743_: *mut leanh::LeanObject,
    mut v_a_2744_: *mut leanh::LeanObject,
    mut v_a_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
    mut v_a_2748_: *mut leanh::LeanObject,
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_a_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2740_);
    v___x_2752_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2752_, 0, v_a_2740_);
    return v___x_2752_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId___boxed(
    mut v_a_2753_: *mut leanh::LeanObject,
    mut v_a_2754_: *mut leanh::LeanObject,
    mut v_a_2755_: *mut leanh::LeanObject,
    mut v_a_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
    mut v_a_2758_: *mut leanh::LeanObject,
    mut v_a_2759_: *mut leanh::LeanObject,
    mut v_a_2760_: *mut leanh::LeanObject,
    mut v_a_2761_: *mut leanh::LeanObject,
    mut v_a_2762_: *mut leanh::LeanObject,
    mut v_a_2763_: *mut leanh::LeanObject,
    mut v_a_2764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2765_ = l_Lean_Meta_Grind_AC_getOpId(
        v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_,
        v_a_2761_, v_a_2762_, v_a_2763_,
    );
    leanh::lean_dec(v_a_2763_);
    leanh::lean_dec_ref(v_a_2762_);
    leanh::lean_dec(v_a_2761_);
    leanh::lean_dec_ref(v_a_2760_);
    leanh::lean_dec(v_a_2759_);
    leanh::lean_dec_ref(v_a_2758_);
    leanh::lean_dec(v_a_2757_);
    leanh::lean_dec_ref(v_a_2756_);
    leanh::lean_dec(v_a_2755_);
    leanh::lean_dec(v_a_2754_);
    leanh::lean_dec(v_a_2753_);
    return v_res_2765_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(
    mut v_msgData_2766_: *mut leanh::LeanObject,
    mut v___y_2767_: *mut leanh::LeanObject,
    mut v___y_2768_: *mut leanh::LeanObject,
    mut v___y_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = lean_st_ref_get(v___y_2770_);
    v_env_2773_ = leanh::lean_ctor_get(v___x_2772_, 0);
    leanh::lean_inc_ref(v_env_2773_);
    leanh::lean_dec(v___x_2772_);
    v___x_2774_ = lean_st_ref_get(v___y_2768_);
    v_mctx_2775_ = leanh::lean_ctor_get(v___x_2774_, 0);
    leanh::lean_inc_ref(v_mctx_2775_);
    leanh::lean_dec(v___x_2774_);
    v_lctx_2776_ = leanh::lean_ctor_get(v___y_2767_, 2);
    v_options_2777_ = leanh::lean_ctor_get(v___y_2769_, 2);
    leanh::lean_inc_ref(v_options_2777_);
    leanh::lean_inc_ref(v_lctx_2776_);
    v___x_2778_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2778_, 0, v_env_2773_);
    leanh::lean_ctor_set(v___x_2778_, 1, v_mctx_2775_);
    leanh::lean_ctor_set(v___x_2778_, 2, v_lctx_2776_);
    leanh::lean_ctor_set(v___x_2778_, 3, v_options_2777_);
    v___x_2779_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2779_, 0, v___x_2778_);
    leanh::lean_ctor_set(v___x_2779_, 1, v_msgData_2766_);
    v___x_2780_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2780_, 0, v___x_2779_);
    return v___x_2780_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0___boxed(
    mut v_msgData_2781_: *mut leanh::LeanObject,
    mut v___y_2782_: *mut leanh::LeanObject,
    mut v___y_2783_: *mut leanh::LeanObject,
    mut v___y_2784_: *mut leanh::LeanObject,
    mut v___y_2785_: *mut leanh::LeanObject,
    mut v___y_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msgData_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
    leanh::lean_dec(v___y_2785_);
    leanh::lean_dec_ref(v___y_2784_);
    leanh::lean_dec(v___y_2783_);
    leanh::lean_dec_ref(v___y_2782_);
    return v_res_2787_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(
    mut v_msg_2788_: *mut leanh::LeanObject,
    mut v___y_2789_: *mut leanh::LeanObject,
    mut v___y_2790_: *mut leanh::LeanObject,
    mut v___y_2791_: *mut leanh::LeanObject,
    mut v___y_2792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2794_ = leanh::lean_ctor_get(v___y_2791_, 5);
                v___x_2795_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
                v_a_2796_ = leanh::lean_ctor_get(v___x_2795_, 0);
                v_isSharedCheck_2804_ = (!leanh::lean_is_exclusive(v___x_2795_)) as u8;
                if v_isSharedCheck_2804_ == 0 {
                    v___x_2798_ = v___x_2795_;
                    v_isShared_2799_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2796_);
                    leanh::lean_dec(v___x_2795_);
                    v___x_2798_ = leanh::lean_box(0);
                    v_isShared_2799_ = v_isSharedCheck_2804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2794_);
                v___x_2800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2800_, 0, v_ref_2794_);
                leanh::lean_ctor_set(v___x_2800_, 1, v_a_2796_);
                if v_isShared_2799_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2798_, 1);
                    leanh::lean_ctor_set(v___x_2798_, 0, v___x_2800_);
                    v___x_2802_ = v___x_2798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
                    v___x_2802_ = v_reuseFailAlloc_2803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg___boxed(
    mut v_msg_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
    mut v___y_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2811_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(
        v_msg_2805_,
        v___y_2806_,
        v___y_2807_,
        v___y_2808_,
        v___y_2809_,
    );
    leanh::lean_dec(v___y_2809_);
    leanh::lean_dec_ref(v___y_2808_);
    leanh::lean_dec(v___y_2807_);
    leanh::lean_dec_ref(v___y_2806_);
    return v_res_2811_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2813_ = l_Lean_Meta_Grind_AC_ACM_getStruct___closed__0;
    v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_getStruct(
    mut v_a_2815_: *mut leanh::LeanObject,
    mut v_a_2816_: *mut leanh::LeanObject,
    mut v_a_2817_: *mut leanh::LeanObject,
    mut v_a_2818_: *mut leanh::LeanObject,
    mut v_a_2819_: *mut leanh::LeanObject,
    mut v_a_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
    mut v_a_2822_: *mut leanh::LeanObject,
    mut v_a_2823_: *mut leanh::LeanObject,
    mut v_a_2824_: *mut leanh::LeanObject,
    mut v_a_2825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v_structs_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_a_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2827_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_2816_, v_a_2824_);
                if leanh::lean_obj_tag(v___x_2827_) == 0 {
                    v_a_2828_ = leanh::lean_ctor_get(v___x_2827_, 0);
                    v_isSharedCheck_2841_ = (!leanh::lean_is_exclusive(v___x_2827_)) as u8;
                    if v_isSharedCheck_2841_ == 0 {
                        v___x_2830_ = v___x_2827_;
                        v_isShared_2831_ = v_isSharedCheck_2841_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2828_);
                        leanh::lean_dec(v___x_2827_);
                        v___x_2830_ = leanh::lean_box(0);
                        v_isShared_2831_ = v_isSharedCheck_2841_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2842_ = leanh::lean_ctor_get(v___x_2827_, 0);
                    v_isSharedCheck_2849_ = (!leanh::lean_is_exclusive(v___x_2827_)) as u8;
                    if v_isSharedCheck_2849_ == 0 {
                        v___x_2844_ = v___x_2827_;
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2842_);
                        leanh::lean_dec(v___x_2827_);
                        v___x_2844_ = leanh::lean_box(0);
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_structs_2832_ = leanh::lean_ctor_get(v_a_2828_, 0);
                leanh::lean_inc_ref(v_structs_2832_);
                leanh::lean_dec(v_a_2828_);
                v___x_2833_ = lean_array_get_size(v_structs_2832_);
                v___x_2834_ = lean_nat_dec_lt(v_a_2815_, v___x_2833_);
                if v___x_2834_ == 0 {
                    leanh::lean_dec_ref(v_structs_2832_);
                    leanh::lean_del_object(v___x_2830_);
                    v___x_2835_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_AC_ACM_getStruct___closed__1,
                    );
                    v___x_2836_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(v___x_2835_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_);
                    return v___x_2836_;
                } else {
                    v___x_2837_ = lean_array_fget(v_structs_2832_, v_a_2815_);
                    leanh::lean_dec_ref(v_structs_2832_);
                    if v_isShared_2831_ == 0 {
                        leanh::lean_ctor_set(v___x_2830_, 0, v___x_2837_);
                        v___x_2839_ = v___x_2830_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2840_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
                        v___x_2839_ = v_reuseFailAlloc_2840_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2839_;
            }
            3 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_ACM_getStruct___boxed(
    mut v_a_2850_: *mut leanh::LeanObject,
    mut v_a_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_a_2855_: *mut leanh::LeanObject,
    mut v_a_2856_: *mut leanh::LeanObject,
    mut v_a_2857_: *mut leanh::LeanObject,
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
    mut v_a_2861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2862_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
        v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_,
        v_a_2858_, v_a_2859_, v_a_2860_,
    );
    leanh::lean_dec(v_a_2860_);
    leanh::lean_dec_ref(v_a_2859_);
    leanh::lean_dec(v_a_2858_);
    leanh::lean_dec_ref(v_a_2857_);
    leanh::lean_dec(v_a_2856_);
    leanh::lean_dec_ref(v_a_2855_);
    leanh::lean_dec(v_a_2854_);
    leanh::lean_dec_ref(v_a_2853_);
    leanh::lean_dec(v_a_2852_);
    leanh::lean_dec(v_a_2851_);
    leanh::lean_dec(v_a_2850_);
    return v_res_2862_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(
    mut v_00_u03b1_2863_: *mut leanh::LeanObject,
    mut v_msg_2864_: *mut leanh::LeanObject,
    mut v___y_2865_: *mut leanh::LeanObject,
    mut v___y_2866_: *mut leanh::LeanObject,
    mut v___y_2867_: *mut leanh::LeanObject,
    mut v___y_2868_: *mut leanh::LeanObject,
    mut v___y_2869_: *mut leanh::LeanObject,
    mut v___y_2870_: *mut leanh::LeanObject,
    mut v___y_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2877_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___redArg(
        v_msg_2864_,
        v___y_2872_,
        v___y_2873_,
        v___y_2874_,
        v___y_2875_,
    );
    return v___x_2877_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0___boxed(
    mut v_00_u03b1_2878_: *mut leanh::LeanObject,
    mut v_msg_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
    mut v___y_2881_: *mut leanh::LeanObject,
    mut v___y_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
    mut v___y_2885_: *mut leanh::LeanObject,
    mut v___y_2886_: *mut leanh::LeanObject,
    mut v___y_2887_: *mut leanh::LeanObject,
    mut v___y_2888_: *mut leanh::LeanObject,
    mut v___y_2889_: *mut leanh::LeanObject,
    mut v___y_2890_: *mut leanh::LeanObject,
    mut v___y_2891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2892_ = l_Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0(
        v_00_u03b1_2878_,
        v_msg_2879_,
        v___y_2880_,
        v___y_2881_,
        v___y_2882_,
        v___y_2883_,
        v___y_2884_,
        v___y_2885_,
        v___y_2886_,
        v___y_2887_,
        v___y_2888_,
        v___y_2889_,
        v___y_2890_,
    );
    leanh::lean_dec(v___y_2890_);
    leanh::lean_dec_ref(v___y_2889_);
    leanh::lean_dec(v___y_2888_);
    leanh::lean_dec_ref(v___y_2887_);
    leanh::lean_dec(v___y_2886_);
    leanh::lean_dec_ref(v___y_2885_);
    leanh::lean_dec(v___y_2884_);
    leanh::lean_dec_ref(v___y_2883_);
    leanh::lean_dec(v___y_2882_);
    leanh::lean_dec(v___y_2881_);
    leanh::lean_dec(v___y_2880_);
    return v_res_2892_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(
    mut v_a_2894_: *mut leanh::LeanObject,
    mut v_f_2895_: *mut leanh::LeanObject,
    mut v_s_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v_v_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2914_: u8 = 0;
    let mut v_unused_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2897_ = leanh::lean_ctor_get(v_s_2896_, 0);
                v_opIdOf_2898_ = leanh::lean_ctor_get(v_s_2896_, 1);
                v_exprToOpIds_2899_ = leanh::lean_ctor_get(v_s_2896_, 2);
                v_steps_2900_ = leanh::lean_ctor_get(v_s_2896_, 3);
                v___x_2901_ = lean_array_get_size(v_structs_2897_);
                v___x_2902_ = lean_nat_dec_lt(v_a_2894_, v___x_2901_);
                if v___x_2902_ == 0 {
                    leanh::lean_dec_ref(v_f_2895_);
                    return v_s_2896_;
                } else {
                    leanh::lean_inc(v_steps_2900_);
                    leanh::lean_inc_ref(v_exprToOpIds_2899_);
                    leanh::lean_inc_ref(v_opIdOf_2898_);
                    leanh::lean_inc_ref(v_structs_2897_);
                    v_isSharedCheck_2914_ = (!leanh::lean_is_exclusive(v_s_2896_)) as u8;
                    if v_isSharedCheck_2914_ == 0 {
                        v_unused_2915_ = leanh::lean_ctor_get(v_s_2896_, 3);
                        leanh::lean_dec(v_unused_2915_);
                        v_unused_2916_ = leanh::lean_ctor_get(v_s_2896_, 2);
                        leanh::lean_dec(v_unused_2916_);
                        v_unused_2917_ = leanh::lean_ctor_get(v_s_2896_, 1);
                        leanh::lean_dec(v_unused_2917_);
                        v_unused_2918_ = leanh::lean_ctor_get(v_s_2896_, 0);
                        leanh::lean_dec(v_unused_2918_);
                        v___x_2904_ = v_s_2896_;
                        v_isShared_2905_ = v_isSharedCheck_2914_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_2896_);
                        v___x_2904_ = leanh::lean_box(0);
                        v_isShared_2905_ = v_isSharedCheck_2914_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2906_ = lean_array_fget(v_structs_2897_, v_a_2894_);
                v___x_2907_ = leanh::lean_box(0);
                v_xs_x27_2908_ = lean_array_fset(v_structs_2897_, v_a_2894_, v___x_2907_);
                v___x_2909_ = leanh::lean_apply_1(v_f_2895_, v_v_2906_);
                v___x_2910_ = lean_array_fset(v_xs_x27_2908_, v_a_2894_, v___x_2909_);
                if v_isShared_2905_ == 0 {
                    leanh::lean_ctor_set(v___x_2904_, 0, v___x_2910_);
                    v___x_2912_ = v___x_2904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_opIdOf_2898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_exprToOpIds_2899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_steps_2900_);
                    v___x_2912_ = v_reuseFailAlloc_2913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed(
    mut v_a_2919_: *mut leanh::LeanObject,
    mut v_f_2920_: *mut leanh::LeanObject,
    mut v_s_2921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2922_ =
        l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0(v_a_2919_, v_f_2920_, v_s_2921_);
    leanh::lean_dec(v_a_2919_);
    return v_res_2922_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg(
    mut v_f_2923_: *mut leanh::LeanObject,
    mut v_a_2924_: *mut leanh::LeanObject,
    mut v_a_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_2924_);
    v___f_2927_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_modifyStruct___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2927_, 0, v_a_2924_);
    leanh::lean_closure_set(v___f_2927_, 1, v_f_2923_);
    v___x_2928_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_2929_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2928_, v___f_2927_, v_a_2925_);
    return v___x_2929_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___redArg___boxed(
    mut v_f_2930_: *mut leanh::LeanObject,
    mut v_a_2931_: *mut leanh::LeanObject,
    mut v_a_2932_: *mut leanh::LeanObject,
    mut v_a_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2934_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_2930_, v_a_2931_, v_a_2932_);
    leanh::lean_dec(v_a_2932_);
    leanh::lean_dec(v_a_2931_);
    return v_res_2934_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct(
    mut v_f_2935_: *mut leanh::LeanObject,
    mut v_a_2936_: *mut leanh::LeanObject,
    mut v_a_2937_: *mut leanh::LeanObject,
    mut v_a_2938_: *mut leanh::LeanObject,
    mut v_a_2939_: *mut leanh::LeanObject,
    mut v_a_2940_: *mut leanh::LeanObject,
    mut v_a_2941_: *mut leanh::LeanObject,
    mut v_a_2942_: *mut leanh::LeanObject,
    mut v_a_2943_: *mut leanh::LeanObject,
    mut v_a_2944_: *mut leanh::LeanObject,
    mut v_a_2945_: *mut leanh::LeanObject,
    mut v_a_2946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(v_f_2935_, v_a_2936_, v_a_2937_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_modifyStruct___boxed(
    mut v_f_2949_: *mut leanh::LeanObject,
    mut v_a_2950_: *mut leanh::LeanObject,
    mut v_a_2951_: *mut leanh::LeanObject,
    mut v_a_2952_: *mut leanh::LeanObject,
    mut v_a_2953_: *mut leanh::LeanObject,
    mut v_a_2954_: *mut leanh::LeanObject,
    mut v_a_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
    mut v_a_2957_: *mut leanh::LeanObject,
    mut v_a_2958_: *mut leanh::LeanObject,
    mut v_a_2959_: *mut leanh::LeanObject,
    mut v_a_2960_: *mut leanh::LeanObject,
    mut v_a_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Meta_Grind_AC_modifyStruct(
        v_f_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_,
        v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_,
    );
    leanh::lean_dec(v_a_2960_);
    leanh::lean_dec_ref(v_a_2959_);
    leanh::lean_dec(v_a_2958_);
    leanh::lean_dec_ref(v_a_2957_);
    leanh::lean_dec(v_a_2956_);
    leanh::lean_dec_ref(v_a_2955_);
    leanh::lean_dec(v_a_2954_);
    leanh::lean_dec_ref(v_a_2953_);
    leanh::lean_dec(v_a_2952_);
    leanh::lean_dec(v_a_2951_);
    leanh::lean_dec(v_a_2950_);
    return v_res_2962_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOp(
    mut v_a_2963_: *mut leanh::LeanObject,
    mut v_a_2964_: *mut leanh::LeanObject,
    mut v_a_2965_: *mut leanh::LeanObject,
    mut v_a_2966_: *mut leanh::LeanObject,
    mut v_a_2967_: *mut leanh::LeanObject,
    mut v_a_2968_: *mut leanh::LeanObject,
    mut v_a_2969_: *mut leanh::LeanObject,
    mut v_a_2970_: *mut leanh::LeanObject,
    mut v_a_2971_: *mut leanh::LeanObject,
    mut v_a_2972_: *mut leanh::LeanObject,
    mut v_a_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v_op_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v_a_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2988_: u8 = 0;
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2975_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_,
                    v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_,
                );
                if leanh::lean_obj_tag(v___x_2975_) == 0 {
                    v_a_2976_ = leanh::lean_ctor_get(v___x_2975_, 0);
                    v_isSharedCheck_2984_ = (!leanh::lean_is_exclusive(v___x_2975_)) as u8;
                    if v_isSharedCheck_2984_ == 0 {
                        v___x_2978_ = v___x_2975_;
                        v_isShared_2979_ = v_isSharedCheck_2984_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2976_);
                        leanh::lean_dec(v___x_2975_);
                        v___x_2978_ = leanh::lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2984_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2985_ = leanh::lean_ctor_get(v___x_2975_, 0);
                    v_isSharedCheck_2992_ = (!leanh::lean_is_exclusive(v___x_2975_)) as u8;
                    if v_isSharedCheck_2992_ == 0 {
                        v___x_2987_ = v___x_2975_;
                        v_isShared_2988_ = v_isSharedCheck_2992_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2985_);
                        leanh::lean_dec(v___x_2975_);
                        v___x_2987_ = leanh::lean_box(0);
                        v_isShared_2988_ = v_isSharedCheck_2992_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_op_2980_ = leanh::lean_ctor_get(v_a_2976_, 3);
                leanh::lean_inc_ref(v_op_2980_);
                leanh::lean_dec(v_a_2976_);
                if v_isShared_2979_ == 0 {
                    leanh::lean_ctor_set(v___x_2978_, 0, v_op_2980_);
                    v___x_2982_ = v___x_2978_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2983_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_op_2980_);
                    v___x_2982_ = v_reuseFailAlloc_2983_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2982_;
            }
            3 => {
                if v_isShared_2988_ == 0 {
                    v___x_2990_ = v___x_2987_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
                    v___x_2990_ = v_reuseFailAlloc_2991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOp___boxed(
    mut v_a_2993_: *mut leanh::LeanObject,
    mut v_a_2994_: *mut leanh::LeanObject,
    mut v_a_2995_: *mut leanh::LeanObject,
    mut v_a_2996_: *mut leanh::LeanObject,
    mut v_a_2997_: *mut leanh::LeanObject,
    mut v_a_2998_: *mut leanh::LeanObject,
    mut v_a_2999_: *mut leanh::LeanObject,
    mut v_a_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
    mut v_a_3002_: *mut leanh::LeanObject,
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_a_3004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3005_ = l_Lean_Meta_Grind_AC_getOp(
        v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
        v_a_3001_, v_a_3002_, v_a_3003_,
    );
    leanh::lean_dec(v_a_3003_);
    leanh::lean_dec_ref(v_a_3002_);
    leanh::lean_dec(v_a_3001_);
    leanh::lean_dec_ref(v_a_3000_);
    leanh::lean_dec(v_a_2999_);
    leanh::lean_dec_ref(v_a_2998_);
    leanh::lean_dec(v_a_2997_);
    leanh::lean_dec_ref(v_a_2996_);
    leanh::lean_dec(v_a_2995_);
    leanh::lean_dec(v_a_2994_);
    leanh::lean_dec(v_a_2993_);
    return v_res_3005_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u64 = 0;
    v___x_3006_ = leanh::lean_unsigned_to_nat(1723);
    v___x_3007_ = lean_uint64_of_nat(v___x_3006_);
    return v___x_3007_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_x_3008_: *mut leanh::LeanObject,
    mut v_x_3009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3018_: u64 = 0;
    let mut v___x_3019_: u64 = 0;
    let mut v___x_3020_: u64 = 0;
    let mut v_fold_3021_: u64 = 0;
    let mut v___x_3022_: u64 = 0;
    let mut v___x_3023_: u64 = 0;
    let mut v___x_3024_: u64 = 0;
    let mut v___x_3025_: usize = 0;
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: usize = 0;
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: u64 = 0;
    let mut v_hash_3037_: u64 = 0;
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3009_) == 0 {
                    return v_x_3008_;
                } else {
                    v_key_3010_ = leanh::lean_ctor_get(v_x_3009_, 0);
                    v_value_3011_ = leanh::lean_ctor_get(v_x_3009_, 1);
                    v_tail_3012_ = leanh::lean_ctor_get(v_x_3009_, 2);
                    v_isSharedCheck_3038_ = (!leanh::lean_is_exclusive(v_x_3009_)) as u8;
                    if v_isSharedCheck_3038_ == 0 {
                        v___x_3014_ = v_x_3009_;
                        v_isShared_3015_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3012_);
                        leanh::lean_inc(v_value_3011_);
                        leanh::lean_inc(v_key_3010_);
                        leanh::lean_dec(v_x_3009_);
                        v___x_3014_ = leanh::lean_box(0);
                        v_isShared_3015_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3016_ = lean_array_get_size(v_x_3008_);
                if leanh::lean_obj_tag(v_key_3010_) == 0 {
                    v___x_3036_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_3018_ = v___x_3036_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3037_ = leanh::lean_ctor_get_uint64(
                        v_key_3010_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3018_ = v_hash_3037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3019_ = 32u64;
                v___x_3020_ = lean_uint64_shift_right(v___y_3018_, v___x_3019_);
                v_fold_3021_ = lean_uint64_xor(v___y_3018_, v___x_3020_);
                v___x_3022_ = 16u64;
                v___x_3023_ = lean_uint64_shift_right(v_fold_3021_, v___x_3022_);
                v___x_3024_ = lean_uint64_xor(v_fold_3021_, v___x_3023_);
                v___x_3025_ = lean_uint64_to_usize(v___x_3024_);
                v___x_3026_ = lean_usize_of_nat(v___x_3016_);
                v___x_3027_ = 1usize;
                v___x_3028_ = lean_usize_sub(v___x_3026_, v___x_3027_);
                v___x_3029_ = lean_usize_land(v___x_3025_, v___x_3028_);
                v___x_3030_ = lean_array_uget_borrowed(v_x_3008_, v___x_3029_);
                leanh::lean_inc(v___x_3030_);
                if v_isShared_3015_ == 0 {
                    leanh::lean_ctor_set(v___x_3014_, 2, v___x_3030_);
                    v___x_3032_ = v___x_3014_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_key_3010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_value_3011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 2, v___x_3030_);
                    v___x_3032_ = v_reuseFailAlloc_3035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3033_ = lean_array_uset(v_x_3008_, v___x_3029_, v___x_3032_);
                v_x_3008_ = v___x_3033_;
                v_x_3009_ = v_tail_3012_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_i_3039_: *mut leanh::LeanObject,
    mut v_source_3040_: *mut leanh::LeanObject,
    mut v_target_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v_es_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3042_ = lean_array_get_size(v_source_3040_);
                v___x_3043_ = lean_nat_dec_lt(v_i_3039_, v___x_3042_);
                if v___x_3043_ == 0 {
                    leanh::lean_dec_ref(v_source_3040_);
                    leanh::lean_dec(v_i_3039_);
                    return v_target_3041_;
                } else {
                    v_es_3044_ = lean_array_fget(v_source_3040_, v_i_3039_);
                    v___x_3045_ = leanh::lean_box(0);
                    v_source_3046_ = lean_array_fset(v_source_3040_, v_i_3039_, v___x_3045_);
                    v_target_3047_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_3041_, v_es_3044_);
                    v___x_3048_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3049_ = lean_nat_add(v_i_3039_, v___x_3048_);
                    leanh::lean_dec(v_i_3039_);
                    v_i_3039_ = v___x_3049_;
                    v_source_3040_ = v_source_3046_;
                    v_target_3041_ = v_target_3047_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(
    mut v_data_3051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3052_ = lean_array_get_size(v_data_3051_);
    v___x_3053_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3054_ = lean_nat_mul(v___x_3052_, v___x_3053_);
    v___x_3055_ = leanh::lean_unsigned_to_nat(0);
    v___x_3056_ = leanh::lean_box(0);
    v___x_3057_ = lean_mk_array(v_nbuckets_3054_, v___x_3056_);
    v___x_3058_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v___x_3055_, v_data_3051_, v___x_3057_);
    return v___x_3058_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(
    mut v_a_3059_: *mut leanh::LeanObject,
    mut v_x_3060_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3061_: u8 = 0;
    let mut v_key_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3060_) == 0 {
                    v___x_3061_ = 0;
                    return v___x_3061_;
                } else {
                    v_key_3062_ = leanh::lean_ctor_get(v_x_3060_, 0);
                    v_tail_3063_ = leanh::lean_ctor_get(v_x_3060_, 2);
                    v___x_3064_ = lean_name_eq(v_key_3062_, v_a_3059_);
                    if v___x_3064_ == 0 {
                        v_x_3060_ = v_tail_3063_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3064_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_3066_: *mut leanh::LeanObject,
    mut v_x_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3068_: u8 = 0;
    let mut v_r_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_3066_, v_x_3067_);
    leanh::lean_dec(v_x_3067_);
    leanh::lean_dec(v_a_3066_);
    v_r_3069_ = leanh::lean_box((v_res_3068_) as usize);
    return v_r_3069_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(
    mut v_m_3070_: *mut leanh::LeanObject,
    mut v_a_3071_: *mut leanh::LeanObject,
    mut v_b_3072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: u64 = 0;
    let mut v___x_3078_: u64 = 0;
    let mut v___x_3079_: u64 = 0;
    let mut v_fold_3080_: u64 = 0;
    let mut v___x_3081_: u64 = 0;
    let mut v___x_3082_: u64 = 0;
    let mut v___x_3083_: u64 = 0;
    let mut v___x_3084_: usize = 0;
    let mut v___x_3085_: usize = 0;
    let mut v___x_3086_: usize = 0;
    let mut v___x_3087_: usize = 0;
    let mut v___x_3088_: usize = 0;
    let mut v_bkt_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: u8 = 0;
    let mut v_val_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut v_unused_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u64 = 0;
    let mut v_hash_3115_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3073_ = leanh::lean_ctor_get(v_m_3070_, 0);
                v_buckets_3074_ = leanh::lean_ctor_get(v_m_3070_, 1);
                v___x_3075_ = lean_array_get_size(v_buckets_3074_);
                if leanh::lean_obj_tag(v_a_3071_) == 0 {
                    v___x_3114_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_3077_ = v___x_3114_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3115_ = leanh::lean_ctor_get_uint64(
                        v_a_3071_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3077_ = v_hash_3115_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3078_ = 32u64;
                v___x_3079_ = lean_uint64_shift_right(v___y_3077_, v___x_3078_);
                v_fold_3080_ = lean_uint64_xor(v___y_3077_, v___x_3079_);
                v___x_3081_ = 16u64;
                v___x_3082_ = lean_uint64_shift_right(v_fold_3080_, v___x_3081_);
                v___x_3083_ = lean_uint64_xor(v_fold_3080_, v___x_3082_);
                v___x_3084_ = lean_uint64_to_usize(v___x_3083_);
                v___x_3085_ = lean_usize_of_nat(v___x_3075_);
                v___x_3086_ = 1usize;
                v___x_3087_ = lean_usize_sub(v___x_3085_, v___x_3086_);
                v___x_3088_ = lean_usize_land(v___x_3084_, v___x_3087_);
                v_bkt_3089_ = lean_array_uget_borrowed(v_buckets_3074_, v___x_3088_);
                v___x_3090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_3071_, v_bkt_3089_);
                if v___x_3090_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3074_);
                    leanh::lean_inc(v_size_3073_);
                    v_isSharedCheck_3111_ = (!leanh::lean_is_exclusive(v_m_3070_)) as u8;
                    if v_isSharedCheck_3111_ == 0 {
                        v_unused_3112_ = leanh::lean_ctor_get(v_m_3070_, 1);
                        leanh::lean_dec(v_unused_3112_);
                        v_unused_3113_ = leanh::lean_ctor_get(v_m_3070_, 0);
                        leanh::lean_dec(v_unused_3113_);
                        v___x_3092_ = v_m_3070_;
                        v_isShared_3093_ = v_isSharedCheck_3111_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3070_);
                        v___x_3092_ = leanh::lean_box(0);
                        v_isShared_3093_ = v_isSharedCheck_3111_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3072_);
                    leanh::lean_dec(v_a_3071_);
                    return v_m_3070_;
                }
            }
            2 => {
                v___x_3094_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3095_ = lean_nat_add(v_size_3073_, v___x_3094_);
                leanh::lean_dec(v_size_3073_);
                leanh::lean_inc(v_bkt_3089_);
                v___x_3096_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3096_, 0, v_a_3071_);
                leanh::lean_ctor_set(v___x_3096_, 1, v_b_3072_);
                leanh::lean_ctor_set(v___x_3096_, 2, v_bkt_3089_);
                v_buckets_x27_3097_ = lean_array_uset(v_buckets_3074_, v___x_3088_, v___x_3096_);
                v___x_3098_ = leanh::lean_unsigned_to_nat(4);
                v___x_3099_ = lean_nat_mul(v_size_x27_3095_, v___x_3098_);
                v___x_3100_ = leanh::lean_unsigned_to_nat(3);
                v___x_3101_ = lean_nat_div(v___x_3099_, v___x_3100_);
                leanh::lean_dec(v___x_3099_);
                v___x_3102_ = lean_array_get_size(v_buckets_x27_3097_);
                v___x_3103_ = lean_nat_dec_le(v___x_3101_, v___x_3102_);
                leanh::lean_dec(v___x_3101_);
                if v___x_3103_ == 0 {
                    v_val_3104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_buckets_x27_3097_);
                    if v_isShared_3093_ == 0 {
                        leanh::lean_ctor_set(v___x_3092_, 1, v_val_3104_);
                        leanh::lean_ctor_set(v___x_3092_, 0, v_size_x27_3095_);
                        v___x_3106_ = v___x_3092_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3107_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_size_x27_3095_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3107_, 1, v_val_3104_);
                        v___x_3106_ = v_reuseFailAlloc_3107_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3093_ == 0 {
                        leanh::lean_ctor_set(v___x_3092_, 1, v_buckets_x27_3097_);
                        leanh::lean_ctor_set(v___x_3092_, 0, v_size_x27_3095_);
                        v___x_3109_ = v___x_3092_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_size_x27_3095_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_buckets_x27_3097_);
                        v___x_3109_ = v_reuseFailAlloc_3110_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3106_;
            }
            4 => {
                return v___x_3109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(
    mut v_as_x27_3116_: *mut leanh::LeanObject,
    mut v_b_3117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3116_) == 0 {
                    return v_b_3117_;
                } else {
                    v_head_3118_ = leanh::lean_ctor_get(v_as_x27_3116_, 0);
                    v_tail_3119_ = leanh::lean_ctor_get(v_as_x27_3116_, 1);
                    v___x_3120_ = leanh::lean_box(0);
                    leanh::lean_inc(v_head_3118_);
                    v_r_3121_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_b_3117_, v_head_3118_, v___x_3120_);
                    v_as_x27_3116_ = v_tail_3119_;
                    v_b_3117_ = v_r_3121_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg___boxed(
    mut v_as_x27_3123_: *mut leanh::LeanObject,
    mut v_b_3124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_3123_, v_b_3124_);
    leanh::lean_dec(v_as_x27_3123_);
    return v_res_3125_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(
    mut v_m_3126_: *mut leanh::LeanObject,
    mut v_l_3127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3128_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_l_3127_, v_m_3126_);
    return v___x_3128_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0___boxed(
    mut v_m_3129_: *mut leanh::LeanObject,
    mut v_l_3130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0(v_m_3129_, v_l_3130_);
    leanh::lean_dec(v_l_3130_);
    return v_res_3131_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3206_ = leanh::lean_box(0);
    v___x_3207_ = leanh::lean_unsigned_to_nat(16);
    v___x_3208_ = lean_mk_array(v___x_3207_, v___x_3206_);
    return v___x_3208_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38()
-> *mut leanh::LeanObject {
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3209_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__37);
    v___x_3210_ = leanh::lean_unsigned_to_nat(0);
    v___x_3211_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3211_, 0, v___x_3210_);
    leanh::lean_ctor_set(v___x_3211_, 1, v___x_3209_);
    return v___x_3211_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3212_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__38);
    v___x_3213_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__36;
    v___x_3214_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v___x_3213_, v___x_3212_);
    return v___x_3214_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc()
-> *mut leanh::LeanObject {
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3215_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc___closed__39);
    return v___x_3215_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0(
    mut v_00_u03b2_3216_: *mut leanh::LeanObject,
    mut v_m_3217_: *mut leanh::LeanObject,
    mut v_a_3218_: *mut leanh::LeanObject,
    mut v_b_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0___redArg(v_m_3217_, v_a_3218_, v_b_3219_);
    return v___x_3220_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(
    mut v_as_3221_: *mut leanh::LeanObject,
    mut v_as_x27_3222_: *mut leanh::LeanObject,
    mut v_b_3223_: *mut leanh::LeanObject,
    mut v_a_3224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3225_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___redArg(v_as_x27_3222_, v_b_3223_);
    return v___x_3225_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1___boxed(
    mut v_as_3226_: *mut leanh::LeanObject,
    mut v_as_x27_3227_: *mut leanh::LeanObject,
    mut v_b_3228_: *mut leanh::LeanObject,
    mut v_a_3229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3230_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__1(v_as_3226_, v_as_x27_3227_, v_b_3228_, v_a_3229_);
    leanh::lean_dec(v_as_x27_3227_);
    leanh::lean_dec(v_as_3226_);
    return v_res_3230_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3231_: *mut leanh::LeanObject,
    mut v_a_3232_: *mut leanh::LeanObject,
    mut v_x_3233_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3234_: u8 = 0;
    v___x_3234_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_3232_, v_x_3233_);
    return v___x_3234_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3235_: *mut leanh::LeanObject,
    mut v_a_3236_: *mut leanh::LeanObject,
    mut v_x_3237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3238_: u8 = 0;
    let mut v_r_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1(v_00_u03b2_3235_, v_a_3236_, v_x_3237_);
    leanh::lean_dec(v_x_3237_);
    leanh::lean_dec(v_a_3236_);
    v_r_3239_ = leanh::lean_box((v_res_3238_) as usize);
    return v_r_3239_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3240_: *mut leanh::LeanObject,
    mut v_data_3241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3242_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2___redArg(v_data_3241_);
    return v___x_3242_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_3243_: *mut leanh::LeanObject,
    mut v_i_3244_: *mut leanh::LeanObject,
    mut v_source_3245_: *mut leanh::LeanObject,
    mut v_target_3246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3247_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3___redArg(v_i_3244_, v_source_3245_, v_target_3246_);
    return v___x_3247_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b2_3248_: *mut leanh::LeanObject,
    mut v_x_3249_: *mut leanh::LeanObject,
    mut v_x_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_3249_, v_x_3250_);
    return v___x_3251_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(
    mut v_op_3277_: *mut leanh::LeanObject,
    mut v_f_3278_: *mut leanh::LeanObject,
    mut v_a_3279_: *mut leanh::LeanObject,
    mut v_a_3280_: *mut leanh::LeanObject,
    mut v_a_3281_: *mut leanh::LeanObject,
    mut v_a_3282_: *mut leanh::LeanObject,
    mut v_a_3283_: *mut leanh::LeanObject,
    mut v_a_3284_: *mut leanh::LeanObject,
    mut v_a_3285_: *mut leanh::LeanObject,
    mut v_a_3286_: *mut leanh::LeanObject,
    mut v_a_3287_: *mut leanh::LeanObject,
    mut v_a_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v_ring_3299_: u8 = 0;
    let mut v___y_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3307_: u8 = 0;
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut v_a_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3316_: u8 = 0;
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3320_: u8 = 0;
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3332_: u8 = 0;
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3337_: u8 = 0;
    let mut v_a_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3341_: u8 = 0;
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3345_: u8 = 0;
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: u8 = 0;
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: u8 = 0;
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: u8 = 0;
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3366_: u8 = 0;
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
                v___x_3294_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3281_);
                if leanh::lean_obj_tag(v___x_3294_) == 0 {
                    v_a_3295_ = leanh::lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3366_ = (!leanh::lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3366_ == 0 {
                        v___x_3297_ = v___x_3294_;
                        v_isShared_3298_ = v_isSharedCheck_3366_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3295_);
                        leanh::lean_dec(v___x_3294_);
                        v___x_3297_ = leanh::lean_box(0);
                        v_isShared_3298_ = v_isSharedCheck_3366_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3367_ = leanh::lean_ctor_get(v___x_3294_, 0);
                    v_isSharedCheck_3374_ = (!leanh::lean_is_exclusive(v___x_3294_)) as u8;
                    if v_isSharedCheck_3374_ == 0 {
                        v___x_3369_ = v___x_3294_;
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3367_);
                        leanh::lean_dec(v___x_3294_);
                        v___x_3369_ = leanh::lean_box(0);
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3291_ = 0;
                v___x_3292_ = leanh::lean_box((v___x_3291_) as usize);
                v___x_3293_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3293_, 0, v___x_3292_);
                return v___x_3293_;
            }
            2 => {
                v_ring_3299_ = leanh::lean_ctor_get_uint8(
                    v_a_3295_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 21) as u32,
                );
                leanh::lean_dec(v_a_3295_);
                if v_ring_3299_ == 0 {
                    v___x_3346_ = leanh::lean_box((v_ring_3299_) as usize);
                    if v_isShared_3298_ == 0 {
                        leanh::lean_ctor_set(v___x_3297_, 0, v___x_3346_);
                        v___x_3348_ = v___x_3297_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
                        v___x_3348_ = v_reuseFailAlloc_3349_;
                        state = 13;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v_f_3278_) == 4 {
                        leanh::lean_del_object(v___x_3297_);
                        v_declName_3350_ = leanh::lean_ctor_get(v_f_3278_, 0);
                        v___x_3351_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__2;
                        v___x_3352_ = lean_name_eq(v_declName_3350_, v___x_3351_);
                        if v___x_3352_ == 0 {
                            v___x_3353_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__5;
                            v___x_3354_ = lean_name_eq(v_declName_3350_, v___x_3353_);
                            if v___x_3354_ == 0 {
                                v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__8;
                                v___x_3356_ = lean_name_eq(v_declName_3350_, v___x_3355_);
                                if v___x_3356_ == 0 {
                                    v___x_3357_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__11;
                                    v___x_3358_ = lean_name_eq(v_declName_3350_, v___x_3357_);
                                    if v___x_3358_ == 0 {
                                        v___x_3359_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___closed__14;
                                        v___x_3360_ = lean_name_eq(v_declName_3350_, v___x_3359_);
                                        if v___x_3360_ == 0 {
                                            state = 1;
                                            continue;
                                        } else {
                                            state = 8;
                                            continue;
                                        }
                                    } else {
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    state = 8;
                                    continue;
                                }
                            } else {
                                state = 8;
                                continue;
                            }
                        } else {
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_3361_ = 0;
                        v___x_3362_ = leanh::lean_box((v___x_3361_) as usize);
                        if v_isShared_3298_ == 0 {
                            leanh::lean_ctor_set(v___x_3297_, 0, v___x_3362_);
                            v___x_3364_ = v___x_3297_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3365_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
                            v___x_3364_ = v_reuseFailAlloc_3365_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_3303_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(
                    v___y_3301_,
                    v_a_3279_,
                    v_a_3280_,
                    v_a_3281_,
                    v_a_3282_,
                    v_a_3283_,
                    v_a_3284_,
                    v_a_3285_,
                    v_a_3286_,
                    v_a_3287_,
                    v_a_3288_,
                );
                if leanh::lean_obj_tag(v___x_3303_) == 0 {
                    v_a_3304_ = leanh::lean_ctor_get(v___x_3303_, 0);
                    v_isSharedCheck_3312_ = (!leanh::lean_is_exclusive(v___x_3303_)) as u8;
                    if v_isSharedCheck_3312_ == 0 {
                        v___x_3306_ = v___x_3303_;
                        v_isShared_3307_ = v_isSharedCheck_3312_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3304_);
                        leanh::lean_dec(v___x_3303_);
                        v___x_3306_ = leanh::lean_box(0);
                        v_isShared_3307_ = v_isSharedCheck_3312_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_3313_ = leanh::lean_ctor_get(v___x_3303_, 0);
                    v_isSharedCheck_3320_ = (!leanh::lean_is_exclusive(v___x_3303_)) as u8;
                    if v_isSharedCheck_3320_ == 0 {
                        v___x_3315_ = v___x_3303_;
                        v_isShared_3316_ = v_isSharedCheck_3320_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3313_);
                        leanh::lean_dec(v___x_3303_);
                        v___x_3315_ = leanh::lean_box(0);
                        v_isShared_3316_ = v_isSharedCheck_3320_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if leanh::lean_obj_tag(v_a_3304_) == 0 {
                    leanh::lean_del_object(v___x_3306_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_a_3304_, 1);
                    if v___y_3302_ == 0 {
                        leanh::lean_del_object(v___x_3306_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3308_ = leanh::lean_box((v_ring_3299_) as usize);
                        if v_isShared_3307_ == 0 {
                            leanh::lean_ctor_set(v___x_3306_, 0, v___x_3308_);
                            v___x_3310_ = v___x_3306_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3311_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3308_);
                            v___x_3310_ = v_reuseFailAlloc_3311_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_3310_;
            }
            6 => {
                if v_isShared_3316_ == 0 {
                    v___x_3318_ = v___x_3315_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3319_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
                    v___x_3318_ = v_reuseFailAlloc_3319_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3318_;
            }
            8 => {
                v___x_3322_ = l_Lean_Expr_getAppNumArgs(v_op_3277_);
                v___x_3323_ = leanh::lean_unsigned_to_nat(4);
                v___x_3324_ = lean_nat_dec_eq(v___x_3322_, v___x_3323_);
                leanh::lean_dec(v___x_3322_);
                if v___x_3324_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_3325_ = l_Lean_Expr_appFn_x21(v_op_3277_);
                    v___x_3326_ = l_Lean_Expr_appFn_x21(v___x_3325_);
                    leanh::lean_dec_ref(v___x_3325_);
                    v___x_3327_ = l_Lean_Expr_appArg_x21(v___x_3326_);
                    leanh::lean_dec_ref(v___x_3326_);
                    leanh::lean_inc_ref(v___x_3327_);
                    v___x_3328_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(
                        v___x_3327_,
                        v_a_3279_,
                        v_a_3280_,
                        v_a_3281_,
                        v_a_3282_,
                        v_a_3283_,
                        v_a_3284_,
                        v_a_3285_,
                        v_a_3286_,
                        v_a_3287_,
                        v_a_3288_,
                    );
                    if leanh::lean_obj_tag(v___x_3328_) == 0 {
                        v_a_3329_ = leanh::lean_ctor_get(v___x_3328_, 0);
                        v_isSharedCheck_3337_ =
                            (!leanh::lean_is_exclusive(v___x_3328_)) as u8;
                        if v_isSharedCheck_3337_ == 0 {
                            v___x_3331_ = v___x_3328_;
                            v_isShared_3332_ = v_isSharedCheck_3337_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3329_);
                            leanh::lean_dec(v___x_3328_);
                            v___x_3331_ = leanh::lean_box(0);
                            v_isShared_3332_ = v_isSharedCheck_3337_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3327_);
                        v_a_3338_ = leanh::lean_ctor_get(v___x_3328_, 0);
                        v_isSharedCheck_3345_ =
                            (!leanh::lean_is_exclusive(v___x_3328_)) as u8;
                        if v_isSharedCheck_3345_ == 0 {
                            v___x_3340_ = v___x_3328_;
                            v_isShared_3341_ = v_isSharedCheck_3345_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3338_);
                            leanh::lean_dec(v___x_3328_);
                            v___x_3340_ = leanh::lean_box(0);
                            v_isShared_3341_ = v_isSharedCheck_3345_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if leanh::lean_obj_tag(v_a_3329_) == 0 {
                    leanh::lean_del_object(v___x_3331_);
                    v___y_3301_ = v___x_3327_;
                    v___y_3302_ = v___x_3324_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_a_3329_, 1);
                    if v___x_3324_ == 0 {
                        leanh::lean_del_object(v___x_3331_);
                        v___y_3301_ = v___x_3327_;
                        v___y_3302_ = v___x_3324_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_3327_);
                        v___x_3333_ = leanh::lean_box((v_ring_3299_) as usize);
                        if v_isShared_3332_ == 0 {
                            leanh::lean_ctor_set(v___x_3331_, 0, v___x_3333_);
                            v___x_3335_ = v___x_3331_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3336_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
                            v___x_3335_ = v_reuseFailAlloc_3336_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            10 => {
                return v___x_3335_;
            }
            11 => {
                if v_isShared_3341_ == 0 {
                    v___x_3343_ = v___x_3340_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3344_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
                    v___x_3343_ = v_reuseFailAlloc_3344_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3343_;
            }
            13 => {
                return v___x_3348_;
            }
            14 => {
                return v___x_3364_;
            }
            15 => {
                if v_isShared_3370_ == 0 {
                    v___x_3372_ = v___x_3369_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
                    v___x_3372_ = v_reuseFailAlloc_3373_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules___boxed(
    mut v_op_3375_: *mut leanh::LeanObject,
    mut v_f_3376_: *mut leanh::LeanObject,
    mut v_a_3377_: *mut leanh::LeanObject,
    mut v_a_3378_: *mut leanh::LeanObject,
    mut v_a_3379_: *mut leanh::LeanObject,
    mut v_a_3380_: *mut leanh::LeanObject,
    mut v_a_3381_: *mut leanh::LeanObject,
    mut v_a_3382_: *mut leanh::LeanObject,
    mut v_a_3383_: *mut leanh::LeanObject,
    mut v_a_3384_: *mut leanh::LeanObject,
    mut v_a_3385_: *mut leanh::LeanObject,
    mut v_a_3386_: *mut leanh::LeanObject,
    mut v_a_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(
            v_op_3375_, v_f_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_,
            v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_,
        );
    leanh::lean_dec(v_a_3386_);
    leanh::lean_dec_ref(v_a_3385_);
    leanh::lean_dec(v_a_3384_);
    leanh::lean_dec_ref(v_a_3383_);
    leanh::lean_dec(v_a_3382_);
    leanh::lean_dec_ref(v_a_3381_);
    leanh::lean_dec(v_a_3380_);
    leanh::lean_dec_ref(v_a_3379_);
    leanh::lean_dec(v_a_3378_);
    leanh::lean_dec(v_a_3377_);
    leanh::lean_dec_ref(v_f_3376_);
    leanh::lean_dec_ref(v_op_3375_);
    return v_res_3388_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(
    mut v_keys_3389_: *mut leanh::LeanObject,
    mut v_vals_3390_: *mut leanh::LeanObject,
    mut v_i_3391_: *mut leanh::LeanObject,
    mut v_k_3392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: u8 = 0;
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3393_ = lean_array_get_size(v_keys_3389_);
                v___x_3394_ = lean_nat_dec_lt(v_i_3391_, v___x_3393_);
                if v___x_3394_ == 0 {
                    leanh::lean_dec(v_i_3391_);
                    v___x_3395_ = leanh::lean_box(0);
                    return v___x_3395_;
                } else {
                    v_k_x27_3396_ = lean_array_fget_borrowed(v_keys_3389_, v_i_3391_);
                    v___x_3397_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_3392_,
                            v_k_x27_3396_,
                        );
                    if v___x_3397_ == 0 {
                        v___x_3398_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3399_ = lean_nat_add(v_i_3391_, v___x_3398_);
                        leanh::lean_dec(v_i_3391_);
                        v_i_3391_ = v___x_3399_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3401_ = lean_array_fget_borrowed(v_vals_3390_, v_i_3391_);
                        leanh::lean_dec(v_i_3391_);
                        leanh::lean_inc(v___x_3401_);
                        v___x_3402_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3402_, 0, v___x_3401_);
                        return v___x_3402_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_3403_: *mut leanh::LeanObject,
    mut v_vals_3404_: *mut leanh::LeanObject,
    mut v_i_3405_: *mut leanh::LeanObject,
    mut v_k_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3407_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_3403_, v_vals_3404_, v_i_3405_, v_k_3406_);
    leanh::lean_dec_ref(v_k_3406_);
    leanh::lean_dec_ref(v_vals_3404_);
    leanh::lean_dec_ref(v_keys_3403_);
    return v_res_3407_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_3408_: usize = 0;
    let mut v___x_3409_: usize = 0;
    let mut v___x_3410_: usize = 0;
    v___x_3408_ = 5usize;
    v___x_3409_ = 1usize;
    v___x_3410_ = lean_usize_shift_left(v___x_3409_, v___x_3408_);
    return v___x_3410_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_3411_: usize = 0;
    let mut v___x_3412_: usize = 0;
    let mut v___x_3413_: usize = 0;
    v___x_3411_ = 1usize;
    v___x_3412_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__0);
    v___x_3413_ = lean_usize_sub(v___x_3412_, v___x_3411_);
    return v___x_3413_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(
    mut v_x_3414_: *mut leanh::LeanObject,
    mut v_x_3415_: usize,
    mut v_x_3416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: usize = 0;
    let mut v___x_3420_: usize = 0;
    let mut v___x_3421_: usize = 0;
    let mut v_j_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: usize = 0;
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3414_) == 0 {
                    v_es_3417_ = leanh::lean_ctor_get(v_x_3414_, 0);
                    v___x_3418_ = leanh::lean_box(2);
                    v___x_3419_ = 5usize;
                    v___x_3420_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1);
                    v___x_3421_ = lean_usize_land(v_x_3415_, v___x_3420_);
                    v_j_3422_ = lean_usize_to_nat(v___x_3421_);
                    v___x_3423_ = lean_array_get_borrowed(v___x_3418_, v_es_3417_, v_j_3422_);
                    leanh::lean_dec(v_j_3422_);
                    match leanh::lean_obj_tag(v___x_3423_) {
                        0 => {
                            v_key_3424_ = leanh::lean_ctor_get(v___x_3423_, 0);
                            v_val_3425_ = leanh::lean_ctor_get(v___x_3423_, 1);
                            v___x_3426_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_3416_, v_key_3424_);
                            if v___x_3426_ == 0 {
                                v___x_3427_ = leanh::lean_box(0);
                                return v___x_3427_;
                            } else {
                                leanh::lean_inc(v_val_3425_);
                                v___x_3428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3428_, 0, v_val_3425_);
                                return v___x_3428_;
                            }
                        }
                        1 => {
                            v_node_3429_ = leanh::lean_ctor_get(v___x_3423_, 0);
                            v___x_3430_ = lean_usize_shift_right(v_x_3415_, v___x_3419_);
                            v_x_3414_ = v_node_3429_;
                            v_x_3415_ = v___x_3430_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3432_ = leanh::lean_box(0);
                            return v___x_3432_;
                        }
                    }
                } else {
                    v_ks_3433_ = leanh::lean_ctor_get(v_x_3414_, 0);
                    v_vs_3434_ = leanh::lean_ctor_get(v_x_3414_, 1);
                    v___x_3435_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3436_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_ks_3433_, v_vs_3434_, v___x_3435_, v_x_3416_);
                    return v___x_3436_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___boxed(
    mut v_x_3437_: *mut leanh::LeanObject,
    mut v_x_3438_: *mut leanh::LeanObject,
    mut v_x_3439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_949__boxed_3440_: usize = 0;
    let mut v_res_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_949__boxed_3440_ = leanh::lean_unbox_usize(v_x_3438_);
    leanh::lean_dec(v_x_3438_);
    v_res_3441_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_3437_, v_x_949__boxed_3440_, v_x_3439_);
    leanh::lean_dec_ref(v_x_3439_);
    leanh::lean_dec_ref(v_x_3437_);
    return v_res_3441_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
    mut v_x_3442_: *mut leanh::LeanObject,
    mut v_x_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3444_: u64 = 0;
    let mut v___x_3445_: usize = 0;
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3443_);
    v___x_3445_ = lean_uint64_to_usize(v___x_3444_);
    v___x_3446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_3442_, v___x_3445_, v_x_3443_);
    return v___x_3446_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg___boxed(
    mut v_x_3447_: *mut leanh::LeanObject,
    mut v_x_3448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3449_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
            v_x_3447_, v_x_3448_,
        );
    leanh::lean_dec_ref(v_x_3448_);
    leanh::lean_dec_ref(v_x_3447_);
    return v_res_3449_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds___redArg(
    mut v_e_3450_: *mut leanh::LeanObject,
    mut v_a_3451_: *mut leanh::LeanObject,
    mut v_a_3452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v_exprToOpIds_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_a_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3454_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_3451_, v_a_3452_);
                if leanh::lean_obj_tag(v___x_3454_) == 0 {
                    v_a_3455_ = leanh::lean_ctor_get(v___x_3454_, 0);
                    v_isSharedCheck_3469_ = (!leanh::lean_is_exclusive(v___x_3454_)) as u8;
                    if v_isSharedCheck_3469_ == 0 {
                        v___x_3457_ = v___x_3454_;
                        v_isShared_3458_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3455_);
                        leanh::lean_dec(v___x_3454_);
                        v___x_3457_ = leanh::lean_box(0);
                        v_isShared_3458_ = v_isSharedCheck_3469_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3470_ = leanh::lean_ctor_get(v___x_3454_, 0);
                    v_isSharedCheck_3477_ = (!leanh::lean_is_exclusive(v___x_3454_)) as u8;
                    if v_isSharedCheck_3477_ == 0 {
                        v___x_3472_ = v___x_3454_;
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3470_);
                        leanh::lean_dec(v___x_3454_);
                        v___x_3472_ = leanh::lean_box(0);
                        v_isShared_3473_ = v_isSharedCheck_3477_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToOpIds_3459_ = leanh::lean_ctor_get(v_a_3455_, 2);
                leanh::lean_inc_ref(v_exprToOpIds_3459_);
                leanh::lean_dec(v_a_3455_);
                v___x_3460_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_exprToOpIds_3459_, v_e_3450_);
                leanh::lean_dec_ref(v_exprToOpIds_3459_);
                if leanh::lean_obj_tag(v___x_3460_) == 0 {
                    v___x_3461_ = leanh::lean_box(0);
                    if v_isShared_3458_ == 0 {
                        leanh::lean_ctor_set(v___x_3457_, 0, v___x_3461_);
                        v___x_3463_ = v___x_3457_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3465_ = leanh::lean_ctor_get(v___x_3460_, 0);
                    leanh::lean_inc(v_val_3465_);
                    leanh::lean_dec_ref_known(v___x_3460_, 1);
                    if v_isShared_3458_ == 0 {
                        leanh::lean_ctor_set(v___x_3457_, 0, v_val_3465_);
                        v___x_3467_ = v___x_3457_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3468_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_val_3465_);
                        v___x_3467_ = v_reuseFailAlloc_3468_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3463_;
            }
            3 => {
                return v___x_3467_;
            }
            4 => {
                if v_isShared_3473_ == 0 {
                    v___x_3475_ = v___x_3472_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
                    v___x_3475_ = v_reuseFailAlloc_3476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds___redArg___boxed(
    mut v_e_3478_: *mut leanh::LeanObject,
    mut v_a_3479_: *mut leanh::LeanObject,
    mut v_a_3480_: *mut leanh::LeanObject,
    mut v_a_3481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3482_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_3478_, v_a_3479_, v_a_3480_);
    leanh::lean_dec_ref(v_a_3480_);
    leanh::lean_dec(v_a_3479_);
    leanh::lean_dec_ref(v_e_3478_);
    return v_res_3482_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds(
    mut v_e_3483_: *mut leanh::LeanObject,
    mut v_a_3484_: *mut leanh::LeanObject,
    mut v_a_3485_: *mut leanh::LeanObject,
    mut v_a_3486_: *mut leanh::LeanObject,
    mut v_a_3487_: *mut leanh::LeanObject,
    mut v_a_3488_: *mut leanh::LeanObject,
    mut v_a_3489_: *mut leanh::LeanObject,
    mut v_a_3490_: *mut leanh::LeanObject,
    mut v_a_3491_: *mut leanh::LeanObject,
    mut v_a_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3495_ = l_Lean_Meta_Grind_AC_getTermOpIds___redArg(v_e_3483_, v_a_3484_, v_a_3492_);
    return v___x_3495_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getTermOpIds___boxed(
    mut v_e_3496_: *mut leanh::LeanObject,
    mut v_a_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
    mut v_a_3499_: *mut leanh::LeanObject,
    mut v_a_3500_: *mut leanh::LeanObject,
    mut v_a_3501_: *mut leanh::LeanObject,
    mut v_a_3502_: *mut leanh::LeanObject,
    mut v_a_3503_: *mut leanh::LeanObject,
    mut v_a_3504_: *mut leanh::LeanObject,
    mut v_a_3505_: *mut leanh::LeanObject,
    mut v_a_3506_: *mut leanh::LeanObject,
    mut v_a_3507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3508_ = l_Lean_Meta_Grind_AC_getTermOpIds(
        v_e_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_,
        v_a_3504_, v_a_3505_, v_a_3506_,
    );
    leanh::lean_dec(v_a_3506_);
    leanh::lean_dec_ref(v_a_3505_);
    leanh::lean_dec(v_a_3504_);
    leanh::lean_dec_ref(v_a_3503_);
    leanh::lean_dec(v_a_3502_);
    leanh::lean_dec_ref(v_a_3501_);
    leanh::lean_dec(v_a_3500_);
    leanh::lean_dec_ref(v_a_3499_);
    leanh::lean_dec(v_a_3498_);
    leanh::lean_dec(v_a_3497_);
    leanh::lean_dec_ref(v_e_3496_);
    return v_res_3508_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(
    mut v_00_u03b2_3509_: *mut leanh::LeanObject,
    mut v_x_3510_: *mut leanh::LeanObject,
    mut v_x_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3512_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
            v_x_3510_, v_x_3511_,
        );
    return v___x_3512_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___boxed(
    mut v_00_u03b2_3513_: *mut leanh::LeanObject,
    mut v_x_3514_: *mut leanh::LeanObject,
    mut v_x_3515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3516_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0(
            v_00_u03b2_3513_,
            v_x_3514_,
            v_x_3515_,
        );
    leanh::lean_dec_ref(v_x_3515_);
    leanh::lean_dec_ref(v_x_3514_);
    return v_res_3516_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(
    mut v_00_u03b2_3517_: *mut leanh::LeanObject,
    mut v_x_3518_: *mut leanh::LeanObject,
    mut v_x_3519_: usize,
    mut v_x_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg(v_x_3518_, v_x_3519_, v_x_3520_);
    return v___x_3521_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___boxed(
    mut v_00_u03b2_3522_: *mut leanh::LeanObject,
    mut v_x_3523_: *mut leanh::LeanObject,
    mut v_x_3524_: *mut leanh::LeanObject,
    mut v_x_3525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1076__boxed_3526_: usize = 0;
    let mut v_res_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1076__boxed_3526_ = leanh::lean_unbox_usize(v_x_3524_);
    leanh::lean_dec(v_x_3524_);
    v_res_3527_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0(v_00_u03b2_3522_, v_x_3523_, v_x_1076__boxed_3526_, v_x_3525_);
    leanh::lean_dec_ref(v_x_3525_);
    leanh::lean_dec_ref(v_x_3523_);
    return v_res_3527_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3528_: *mut leanh::LeanObject,
    mut v_keys_3529_: *mut leanh::LeanObject,
    mut v_vals_3530_: *mut leanh::LeanObject,
    mut v_heq_3531_: *mut leanh::LeanObject,
    mut v_i_3532_: *mut leanh::LeanObject,
    mut v_k_3533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3534_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___redArg(v_keys_3529_, v_vals_3530_, v_i_3532_, v_k_3533_);
    return v___x_3534_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3535_: *mut leanh::LeanObject,
    mut v_keys_3536_: *mut leanh::LeanObject,
    mut v_vals_3537_: *mut leanh::LeanObject,
    mut v_heq_3538_: *mut leanh::LeanObject,
    mut v_i_3539_: *mut leanh::LeanObject,
    mut v_k_3540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3541_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0_spec__1(v_00_u03b2_3535_, v_keys_3536_, v_vals_3537_, v_heq_3538_, v_i_3539_, v_k_3540_);
    leanh::lean_dec_ref(v_k_3540_);
    leanh::lean_dec_ref(v_vals_3537_);
    leanh::lean_dec_ref(v_keys_3536_);
    return v_res_3541_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(
    mut v_opId_3542_: *mut leanh::LeanObject,
    mut v_a_3543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: u8 = 0;
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3551_: u8 = 0;
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_unused_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3543_) == 0 {
                    v___x_3544_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3544_, 0, v_opId_3542_);
                    leanh::lean_ctor_set(v___x_3544_, 1, v_a_3543_);
                    return v___x_3544_;
                } else {
                    v_head_3545_ = leanh::lean_ctor_get(v_a_3543_, 0);
                    v_tail_3546_ = leanh::lean_ctor_get(v_a_3543_, 1);
                    v___x_3547_ = lean_nat_dec_lt(v_opId_3542_, v_head_3545_);
                    if v___x_3547_ == 0 {
                        leanh::lean_inc(v_tail_3546_);
                        leanh::lean_inc(v_head_3545_);
                        v_isSharedCheck_3559_ = (!leanh::lean_is_exclusive(v_a_3543_)) as u8;
                        if v_isSharedCheck_3559_ == 0 {
                            v_unused_3560_ = leanh::lean_ctor_get(v_a_3543_, 1);
                            leanh::lean_dec(v_unused_3560_);
                            v_unused_3561_ = leanh::lean_ctor_get(v_a_3543_, 0);
                            leanh::lean_dec(v_unused_3561_);
                            v___x_3549_ = v_a_3543_;
                            v_isShared_3550_ = v_isSharedCheck_3559_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_3543_);
                            v___x_3549_ = leanh::lean_box(0);
                            v_isShared_3550_ = v_isSharedCheck_3559_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_3562_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3562_, 0, v_opId_3542_);
                        leanh::lean_ctor_set(v___x_3562_, 1, v_a_3543_);
                        return v___x_3562_;
                    }
                }
            }
            1 => {
                v___x_3551_ = lean_nat_dec_eq(v_opId_3542_, v_head_3545_);
                if v___x_3551_ == 0 {
                    v___x_3552_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(v_opId_3542_, v_tail_3546_);
                    if v_isShared_3550_ == 0 {
                        leanh::lean_ctor_set(v___x_3549_, 1, v___x_3552_);
                        v___x_3554_ = v___x_3549_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3555_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_head_3545_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 1, v___x_3552_);
                        v___x_3554_ = v_reuseFailAlloc_3555_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_head_3545_);
                    if v_isShared_3550_ == 0 {
                        leanh::lean_ctor_set(v___x_3549_, 0, v_opId_3542_);
                        v___x_3557_ = v___x_3549_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3558_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_opId_3542_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_tail_3546_);
                        v___x_3557_ = v_reuseFailAlloc_3558_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3554_;
            }
            3 => {
                return v___x_3557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_3563_: *mut leanh::LeanObject,
    mut v_x_3564_: *mut leanh::LeanObject,
    mut v_x_3565_: *mut leanh::LeanObject,
    mut v_x_3566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3571_: u8 = 0;
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: u8 = 0;
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: u8 = 0;
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3567_ = leanh::lean_ctor_get(v_x_3563_, 0);
                v_vs_3568_ = leanh::lean_ctor_get(v_x_3563_, 1);
                v_isSharedCheck_3592_ = (!leanh::lean_is_exclusive(v_x_3563_)) as u8;
                if v_isSharedCheck_3592_ == 0 {
                    v___x_3570_ = v_x_3563_;
                    v_isShared_3571_ = v_isSharedCheck_3592_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3568_);
                    leanh::lean_inc(v_ks_3567_);
                    leanh::lean_dec(v_x_3563_);
                    v___x_3570_ = leanh::lean_box(0);
                    v_isShared_3571_ = v_isSharedCheck_3592_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3572_ = lean_array_get_size(v_ks_3567_);
                v___x_3573_ = lean_nat_dec_lt(v_x_3564_, v___x_3572_);
                if v___x_3573_ == 0 {
                    leanh::lean_dec(v_x_3564_);
                    v___x_3574_ = lean_array_push(v_ks_3567_, v_x_3565_);
                    v___x_3575_ = lean_array_push(v_vs_3568_, v_x_3566_);
                    if v_isShared_3571_ == 0 {
                        leanh::lean_ctor_set(v___x_3570_, 1, v___x_3575_);
                        leanh::lean_ctor_set(v___x_3570_, 0, v___x_3574_);
                        v___x_3577_ = v___x_3570_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3578_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___x_3574_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3575_);
                        v___x_3577_ = v_reuseFailAlloc_3578_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3579_ = lean_array_fget_borrowed(v_ks_3567_, v_x_3564_);
                    v___x_3580_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_3565_,
                            v_k_x27_3579_,
                        );
                    if v___x_3580_ == 0 {
                        if v_isShared_3571_ == 0 {
                            v___x_3582_ = v___x_3570_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3586_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_ks_3567_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_vs_3568_);
                            v___x_3582_ = v_reuseFailAlloc_3586_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3587_ = lean_array_fset(v_ks_3567_, v_x_3564_, v_x_3565_);
                        v___x_3588_ = lean_array_fset(v_vs_3568_, v_x_3564_, v_x_3566_);
                        leanh::lean_dec(v_x_3564_);
                        if v_isShared_3571_ == 0 {
                            leanh::lean_ctor_set(v___x_3570_, 1, v___x_3588_);
                            leanh::lean_ctor_set(v___x_3570_, 0, v___x_3587_);
                            v___x_3590_ = v___x_3570_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3591_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3587_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3588_);
                            v___x_3590_ = v_reuseFailAlloc_3591_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3577_;
            }
            3 => {
                v___x_3583_ = leanh::lean_unsigned_to_nat(1);
                v___x_3584_ = lean_nat_add(v_x_3564_, v___x_3583_);
                leanh::lean_dec(v_x_3564_);
                v_x_3563_ = v___x_3582_;
                v_x_3564_ = v___x_3584_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(
    mut v_n_3593_: *mut leanh::LeanObject,
    mut v_k_3594_: *mut leanh::LeanObject,
    mut v_v_3595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3596_ = leanh::lean_unsigned_to_nat(0);
    v___x_3597_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_3593_, v___x_3596_, v_k_3594_, v_v_3595_);
    return v___x_3597_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3598_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3598_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(
    mut v_x_3599_: *mut leanh::LeanObject,
    mut v_x_3600_: usize,
    mut v_x_3601_: usize,
    mut v_x_3602_: *mut leanh::LeanObject,
    mut v_x_3603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: usize = 0;
    let mut v___x_3606_: usize = 0;
    let mut v___x_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v_j_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: u8 = 0;
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v_v_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3628_: u8 = 0;
    let mut v___x_3629_: u8 = 0;
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v_node_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3640_: usize = 0;
    let mut v___x_3641_: usize = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_unused_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3659_: u8 = 0;
    let mut v_ks_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: usize = 0;
    let mut v___x_3666_: u8 = 0;
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: u8 = 0;
    let mut v_reuseFailAlloc_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3599_) == 0 {
                    v_es_3604_ = leanh::lean_ctor_get(v_x_3599_, 0);
                    v___x_3605_ = 5usize;
                    v___x_3606_ = 1usize;
                    v___x_3607_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0_spec__0___redArg___closed__1);
                    v___x_3608_ = lean_usize_land(v_x_3600_, v___x_3607_);
                    v_j_3609_ = lean_usize_to_nat(v___x_3608_);
                    v___x_3610_ = lean_array_get_size(v_es_3604_);
                    v___x_3611_ = lean_nat_dec_lt(v_j_3609_, v___x_3610_);
                    if v___x_3611_ == 0 {
                        leanh::lean_dec(v_j_3609_);
                        leanh::lean_dec(v_x_3603_);
                        leanh::lean_dec_ref(v_x_3602_);
                        return v_x_3599_;
                    } else {
                        leanh::lean_inc_ref(v_es_3604_);
                        v_isSharedCheck_3648_ = (!leanh::lean_is_exclusive(v_x_3599_)) as u8;
                        if v_isSharedCheck_3648_ == 0 {
                            v_unused_3649_ = leanh::lean_ctor_get(v_x_3599_, 0);
                            leanh::lean_dec(v_unused_3649_);
                            v___x_3613_ = v_x_3599_;
                            v_isShared_3614_ = v_isSharedCheck_3648_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3599_);
                            v___x_3613_ = leanh::lean_box(0);
                            v_isShared_3614_ = v_isSharedCheck_3648_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3650_ = leanh::lean_ctor_get(v_x_3599_, 0);
                    v_vs_3651_ = leanh::lean_ctor_get(v_x_3599_, 1);
                    v_isSharedCheck_3671_ = (!leanh::lean_is_exclusive(v_x_3599_)) as u8;
                    if v_isSharedCheck_3671_ == 0 {
                        v___x_3653_ = v_x_3599_;
                        v_isShared_3654_ = v_isSharedCheck_3671_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3651_);
                        leanh::lean_inc(v_ks_3650_);
                        leanh::lean_dec(v_x_3599_);
                        v___x_3653_ = leanh::lean_box(0);
                        v_isShared_3654_ = v_isSharedCheck_3671_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3615_ = lean_array_fget(v_es_3604_, v_j_3609_);
                v___x_3616_ = leanh::lean_box(0);
                v_xs_x27_3617_ = lean_array_fset(v_es_3604_, v_j_3609_, v___x_3616_);
                match leanh::lean_obj_tag(v_v_3615_) {
                    0 => {
                        v_key_3624_ = leanh::lean_ctor_get(v_v_3615_, 0);
                        v_val_3625_ = leanh::lean_ctor_get(v_v_3615_, 1);
                        v_isSharedCheck_3635_ = (!leanh::lean_is_exclusive(v_v_3615_)) as u8;
                        if v_isSharedCheck_3635_ == 0 {
                            v___x_3627_ = v_v_3615_;
                            v_isShared_3628_ = v_isSharedCheck_3635_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3625_);
                            leanh::lean_inc(v_key_3624_);
                            leanh::lean_dec(v_v_3615_);
                            v___x_3627_ = leanh::lean_box(0);
                            v_isShared_3628_ = v_isSharedCheck_3635_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3636_ = leanh::lean_ctor_get(v_v_3615_, 0);
                        v_isSharedCheck_3646_ = (!leanh::lean_is_exclusive(v_v_3615_)) as u8;
                        if v_isSharedCheck_3646_ == 0 {
                            v___x_3638_ = v_v_3615_;
                            v_isShared_3639_ = v_isSharedCheck_3646_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3636_);
                            leanh::lean_dec(v_v_3615_);
                            v___x_3638_ = leanh::lean_box(0);
                            v_isShared_3639_ = v_isSharedCheck_3646_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3647_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3647_, 0, v_x_3602_);
                        leanh::lean_ctor_set(v___x_3647_, 1, v_x_3603_);
                        v___y_3619_ = v___x_3647_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3620_ = lean_array_fset(v_xs_x27_3617_, v_j_3609_, v___y_3619_);
                leanh::lean_dec(v_j_3609_);
                if v_isShared_3614_ == 0 {
                    leanh::lean_ctor_set(v___x_3613_, 0, v___x_3620_);
                    v___x_3622_ = v___x_3613_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3622_;
            }
            4 => {
                v___x_3629_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_3602_,
                        v_key_3624_,
                    );
                if v___x_3629_ == 0 {
                    leanh::lean_del_object(v___x_3627_);
                    v___x_3630_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3624_,
                        v_val_3625_,
                        v_x_3602_,
                        v_x_3603_,
                    );
                    v___x_3631_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3631_, 0, v___x_3630_);
                    v___y_3619_ = v___x_3631_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3625_);
                    leanh::lean_dec(v_key_3624_);
                    if v_isShared_3628_ == 0 {
                        leanh::lean_ctor_set(v___x_3627_, 1, v_x_3603_);
                        leanh::lean_ctor_set(v___x_3627_, 0, v_x_3602_);
                        v___x_3633_ = v___x_3627_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3634_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_x_3602_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_x_3603_);
                        v___x_3633_ = v_reuseFailAlloc_3634_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3619_ = v___x_3633_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3640_ = lean_usize_shift_right(v_x_3600_, v___x_3605_);
                v___x_3641_ = lean_usize_add(v_x_3601_, v___x_3606_);
                v___x_3642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_node_3636_, v___x_3640_, v___x_3641_, v_x_3602_, v_x_3603_);
                if v_isShared_3639_ == 0 {
                    leanh::lean_ctor_set(v___x_3638_, 0, v___x_3642_);
                    v___x_3644_ = v___x_3638_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3619_ = v___x_3644_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3654_ == 0 {
                    v___x_3656_ = v___x_3653_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_ks_3650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_vs_3651_);
                    v___x_3656_ = v_reuseFailAlloc_3670_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3657_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v___x_3656_, v_x_3602_, v_x_3603_);
                v___x_3665_ = 7usize;
                v___x_3666_ = lean_usize_dec_le(v___x_3665_, v_x_3601_);
                if v___x_3666_ == 0 {
                    v___x_3667_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3657_);
                    v___x_3668_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3669_ = lean_nat_dec_lt(v___x_3667_, v___x_3668_);
                    leanh::lean_dec(v___x_3667_);
                    v___y_3659_ = v___x_3669_;
                    state = 10;
                    continue;
                } else {
                    v___y_3659_ = v___x_3666_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3659_ == 0 {
                    v_ks_3660_ = leanh::lean_ctor_get(v_newNode_3657_, 0);
                    leanh::lean_inc_ref(v_ks_3660_);
                    v_vs_3661_ = leanh::lean_ctor_get(v_newNode_3657_, 1);
                    leanh::lean_inc_ref(v_vs_3661_);
                    leanh::lean_dec_ref(v_newNode_3657_);
                    v___x_3662_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3663_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___closed__0);
                    v___x_3664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_x_3601_, v_ks_3660_, v_vs_3661_, v___x_3662_, v___x_3663_);
                    leanh::lean_dec_ref(v_vs_3661_);
                    leanh::lean_dec_ref(v_ks_3660_);
                    return v___x_3664_;
                } else {
                    return v_newNode_3657_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(
    mut v_depth_3672_: usize,
    mut v_keys_3673_: *mut leanh::LeanObject,
    mut v_vals_3674_: *mut leanh::LeanObject,
    mut v_i_3675_: *mut leanh::LeanObject,
    mut v_entries_3676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: u8 = 0;
    let mut v_k_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u64 = 0;
    let mut v_h_3682_: usize = 0;
    let mut v___x_3683_: usize = 0;
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: usize = 0;
    let mut v___x_3686_: usize = 0;
    let mut v___x_3687_: usize = 0;
    let mut v_h_3688_: usize = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3677_ = lean_array_get_size(v_keys_3673_);
                v___x_3678_ = lean_nat_dec_lt(v_i_3675_, v___x_3677_);
                if v___x_3678_ == 0 {
                    leanh::lean_dec(v_i_3675_);
                    return v_entries_3676_;
                } else {
                    v_k_3679_ = lean_array_fget_borrowed(v_keys_3673_, v_i_3675_);
                    v_v_3680_ = lean_array_fget_borrowed(v_vals_3674_, v_i_3675_);
                    v___x_3681_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_3679_);
                    v_h_3682_ = lean_uint64_to_usize(v___x_3681_);
                    v___x_3683_ = 5usize;
                    v___x_3684_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3685_ = 1usize;
                    v___x_3686_ = lean_usize_sub(v_depth_3672_, v___x_3685_);
                    v___x_3687_ = lean_usize_mul(v___x_3683_, v___x_3686_);
                    v_h_3688_ = lean_usize_shift_right(v_h_3682_, v___x_3687_);
                    v___x_3689_ = lean_nat_add(v_i_3675_, v___x_3684_);
                    leanh::lean_dec(v_i_3675_);
                    leanh::lean_inc(v_v_3680_);
                    leanh::lean_inc(v_k_3679_);
                    v___x_3690_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_entries_3676_, v_h_3688_, v_depth_3672_, v_k_3679_, v_v_3680_);
                    v_i_3675_ = v___x_3689_;
                    v_entries_3676_ = v___x_3690_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_3692_: *mut leanh::LeanObject,
    mut v_keys_3693_: *mut leanh::LeanObject,
    mut v_vals_3694_: *mut leanh::LeanObject,
    mut v_i_3695_: *mut leanh::LeanObject,
    mut v_entries_3696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3697_: usize = 0;
    let mut v_res_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3697_ = leanh::lean_unbox_usize(v_depth_3692_);
    leanh::lean_dec(v_depth_3692_);
    v_res_3698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_3697_, v_keys_3693_, v_vals_3694_, v_i_3695_, v_entries_3696_);
    leanh::lean_dec_ref(v_vals_3694_);
    leanh::lean_dec_ref(v_keys_3693_);
    return v_res_3698_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg___boxed(
    mut v_x_3699_: *mut leanh::LeanObject,
    mut v_x_3700_: *mut leanh::LeanObject,
    mut v_x_3701_: *mut leanh::LeanObject,
    mut v_x_3702_: *mut leanh::LeanObject,
    mut v_x_3703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_398__boxed_3704_: usize = 0;
    let mut v_x_399__boxed_3705_: usize = 0;
    let mut v_res_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_398__boxed_3704_ = leanh::lean_unbox_usize(v_x_3700_);
    leanh::lean_dec(v_x_3700_);
    v_x_399__boxed_3705_ = leanh::lean_unbox_usize(v_x_3701_);
    leanh::lean_dec(v_x_3701_);
    v_res_3706_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_3699_, v_x_398__boxed_3704_, v_x_399__boxed_3705_, v_x_3702_, v_x_3703_);
    return v_res_3706_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(
    mut v_x_3707_: *mut leanh::LeanObject,
    mut v_x_3708_: *mut leanh::LeanObject,
    mut v_x_3709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3710_: u64 = 0;
    let mut v___x_3711_: usize = 0;
    let mut v___x_3712_: usize = 0;
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3710_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_3708_);
    v___x_3711_ = lean_uint64_to_usize(v___x_3710_);
    v___x_3712_ = 1usize;
    v___x_3713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_3707_, v___x_3711_, v___x_3712_, v_x_3708_, v_x_3709_);
    return v___x_3713_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(
    mut v_m_3714_: *mut leanh::LeanObject,
    mut v_e_3715_: *mut leanh::LeanObject,
    mut v_opId_3716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3717_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(
            v_m_3714_, v_e_3715_,
        );
    if leanh::lean_obj_tag(v___x_3717_) == 1 {
        let mut v_val_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3718_ = leanh::lean_ctor_get(v___x_3717_, 0);
        leanh::lean_inc(v_val_3718_);
        leanh::lean_dec_ref_known(v___x_3717_, 1);
        v___x_3719_ =
            l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_go(
                v_opId_3716_,
                v_val_3718_,
            );
        v___x_3720_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_3714_, v_e_3715_, v___x_3719_);
        return v___x_3720_;
    } else {
        let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3717_);
        v___x_3721_ = leanh::lean_box(0);
        v___x_3722_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3722_, 0, v_opId_3716_);
        leanh::lean_ctor_set(v___x_3722_, 1, v___x_3721_);
        v___x_3723_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_m_3714_, v_e_3715_, v___x_3722_);
        return v___x_3723_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0(
    mut v_00_u03b2_3724_: *mut leanh::LeanObject,
    mut v_x_3725_: *mut leanh::LeanObject,
    mut v_x_3726_: *mut leanh::LeanObject,
    mut v_x_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_x_3725_, v_x_3726_, v_x_3727_);
    return v___x_3728_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(
    mut v_00_u03b2_3729_: *mut leanh::LeanObject,
    mut v_x_3730_: *mut leanh::LeanObject,
    mut v_x_3731_: usize,
    mut v_x_3732_: usize,
    mut v_x_3733_: *mut leanh::LeanObject,
    mut v_x_3734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___redArg(v_x_3730_, v_x_3731_, v_x_3732_, v_x_3733_, v_x_3734_);
    return v___x_3735_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0___boxed(
    mut v_00_u03b2_3736_: *mut leanh::LeanObject,
    mut v_x_3737_: *mut leanh::LeanObject,
    mut v_x_3738_: *mut leanh::LeanObject,
    mut v_x_3739_: *mut leanh::LeanObject,
    mut v_x_3740_: *mut leanh::LeanObject,
    mut v_x_3741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_590__boxed_3742_: usize = 0;
    let mut v_x_591__boxed_3743_: usize = 0;
    let mut v_res_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_590__boxed_3742_ = leanh::lean_unbox_usize(v_x_3738_);
    leanh::lean_dec(v_x_3738_);
    v_x_591__boxed_3743_ = leanh::lean_unbox_usize(v_x_3739_);
    leanh::lean_dec(v_x_3739_);
    v_res_3744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0(v_00_u03b2_3736_, v_x_3737_, v_x_590__boxed_3742_, v_x_591__boxed_3743_, v_x_3740_, v_x_3741_);
    return v_res_3744_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3745_: *mut leanh::LeanObject,
    mut v_n_3746_: *mut leanh::LeanObject,
    mut v_k_3747_: *mut leanh::LeanObject,
    mut v_v_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3749_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1___redArg(v_n_3746_, v_k_3747_, v_v_3748_);
    return v___x_3749_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3750_: *mut leanh::LeanObject,
    mut v_depth_3751_: usize,
    mut v_keys_3752_: *mut leanh::LeanObject,
    mut v_vals_3753_: *mut leanh::LeanObject,
    mut v_heq_3754_: *mut leanh::LeanObject,
    mut v_i_3755_: *mut leanh::LeanObject,
    mut v_entries_3756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___redArg(v_depth_3751_, v_keys_3752_, v_vals_3753_, v_i_3755_, v_entries_3756_);
    return v___x_3757_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3758_: *mut leanh::LeanObject,
    mut v_depth_3759_: *mut leanh::LeanObject,
    mut v_keys_3760_: *mut leanh::LeanObject,
    mut v_vals_3761_: *mut leanh::LeanObject,
    mut v_heq_3762_: *mut leanh::LeanObject,
    mut v_i_3763_: *mut leanh::LeanObject,
    mut v_entries_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3765_: usize = 0;
    let mut v_res_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3765_ = leanh::lean_unbox_usize(v_depth_3759_);
    leanh::lean_dec(v_depth_3759_);
    v_res_3766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__2(v_00_u03b2_3758_, v_depth_boxed_3765_, v_keys_3760_, v_vals_3761_, v_heq_3762_, v_i_3763_, v_entries_3764_);
    leanh::lean_dec_ref(v_vals_3761_);
    leanh::lean_dec_ref(v_keys_3760_);
    return v_res_3766_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3767_: *mut leanh::LeanObject,
    mut v_x_3768_: *mut leanh::LeanObject,
    mut v_x_3769_: *mut leanh::LeanObject,
    mut v_x_3770_: *mut leanh::LeanObject,
    mut v_x_3771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3772_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3768_, v_x_3769_, v_x_3770_, v_x_3771_);
    return v___x_3772_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(
    mut v_e_3773_: *mut leanh::LeanObject,
    mut v_a_3774_: *mut leanh::LeanObject,
    mut v_s_3775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3776_ = leanh::lean_ctor_get(v_s_3775_, 0);
                v_opIdOf_3777_ = leanh::lean_ctor_get(v_s_3775_, 1);
                v_exprToOpIds_3778_ = leanh::lean_ctor_get(v_s_3775_, 2);
                v_steps_3779_ = leanh::lean_ctor_get(v_s_3775_, 3);
                v_isSharedCheck_3787_ = (!leanh::lean_is_exclusive(v_s_3775_)) as u8;
                if v_isSharedCheck_3787_ == 0 {
                    v___x_3781_ = v_s_3775_;
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_3779_);
                    leanh::lean_inc(v_exprToOpIds_3778_);
                    leanh::lean_inc(v_opIdOf_3777_);
                    leanh::lean_inc(v_structs_3776_);
                    leanh::lean_dec(v_s_3775_);
                    v___x_3781_ = leanh::lean_box(0);
                    v_isShared_3782_ = v_isSharedCheck_3787_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_3774_);
                v___x_3783_ =
                    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId(
                        v_exprToOpIds_3778_,
                        v_e_3773_,
                        v_a_3774_,
                    );
                if v_isShared_3782_ == 0 {
                    leanh::lean_ctor_set(v___x_3781_, 2, v___x_3783_);
                    v___x_3785_ = v___x_3781_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_structs_3776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_opIdOf_3777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 2, v___x_3783_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 3, v_steps_3779_);
                    v___x_3785_ = v_reuseFailAlloc_3786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3785_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed(
    mut v_e_3788_: *mut leanh::LeanObject,
    mut v_a_3789_: *mut leanh::LeanObject,
    mut v_s_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ =
        l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0(v_e_3788_, v_a_3789_, v_s_3790_);
    leanh::lean_dec(v_a_3789_);
    return v_res_3791_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg(
    mut v_e_3792_: *mut leanh::LeanObject,
    mut v_a_3793_: *mut leanh::LeanObject,
    mut v_a_3794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_3793_);
    v___f_3796_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_AC_addTermOpId___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3796_, 0, v_e_3792_);
    leanh::lean_closure_set(v___f_3796_, 1, v_a_3793_);
    v___x_3797_ = l_Lean_Meta_Grind_AC_acExt;
    v___x_3798_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3797_, v___f_3796_, v_a_3794_);
    return v___x_3798_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___redArg___boxed(
    mut v_e_3799_: *mut leanh::LeanObject,
    mut v_a_3800_: *mut leanh::LeanObject,
    mut v_a_3801_: *mut leanh::LeanObject,
    mut v_a_3802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3803_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_3799_, v_a_3800_, v_a_3801_);
    leanh::lean_dec(v_a_3801_);
    leanh::lean_dec(v_a_3800_);
    return v_res_3803_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId(
    mut v_e_3804_: *mut leanh::LeanObject,
    mut v_a_3805_: *mut leanh::LeanObject,
    mut v_a_3806_: *mut leanh::LeanObject,
    mut v_a_3807_: *mut leanh::LeanObject,
    mut v_a_3808_: *mut leanh::LeanObject,
    mut v_a_3809_: *mut leanh::LeanObject,
    mut v_a_3810_: *mut leanh::LeanObject,
    mut v_a_3811_: *mut leanh::LeanObject,
    mut v_a_3812_: *mut leanh::LeanObject,
    mut v_a_3813_: *mut leanh::LeanObject,
    mut v_a_3814_: *mut leanh::LeanObject,
    mut v_a_3815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_3804_, v_a_3805_, v_a_3806_);
    return v___x_3817_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_addTermOpId___boxed(
    mut v_e_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
    mut v_a_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_a_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
    mut v_a_3824_: *mut leanh::LeanObject,
    mut v_a_3825_: *mut leanh::LeanObject,
    mut v_a_3826_: *mut leanh::LeanObject,
    mut v_a_3827_: *mut leanh::LeanObject,
    mut v_a_3828_: *mut leanh::LeanObject,
    mut v_a_3829_: *mut leanh::LeanObject,
    mut v_a_3830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3831_ = l_Lean_Meta_Grind_AC_addTermOpId(
        v_e_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_,
        v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_,
    );
    leanh::lean_dec(v_a_3829_);
    leanh::lean_dec_ref(v_a_3828_);
    leanh::lean_dec(v_a_3827_);
    leanh::lean_dec_ref(v_a_3826_);
    leanh::lean_dec(v_a_3825_);
    leanh::lean_dec_ref(v_a_3824_);
    leanh::lean_dec(v_a_3823_);
    leanh::lean_dec_ref(v_a_3822_);
    leanh::lean_dec(v_a_3821_);
    leanh::lean_dec(v_a_3820_);
    leanh::lean_dec(v_a_3819_);
    return v_res_3831_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_mkVar___lam__0(
    mut v_e_3832_: *mut leanh::LeanObject,
    mut v_size_3833_: *mut leanh::LeanObject,
    mut v_s_3834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assocInst_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commInst_x3f_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutralInst_x3f_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_3852_: u8 = 0;
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3855_: u8 = 0;
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_3835_ = leanh::lean_ctor_get(v_s_3834_, 0);
                v_type_3836_ = leanh::lean_ctor_get(v_s_3834_, 1);
                v_u_3837_ = leanh::lean_ctor_get(v_s_3834_, 2);
                v_op_3838_ = leanh::lean_ctor_get(v_s_3834_, 3);
                v_neutral_x3f_3839_ = leanh::lean_ctor_get(v_s_3834_, 4);
                v_assocInst_3840_ = leanh::lean_ctor_get(v_s_3834_, 5);
                v_idempotentInst_x3f_3841_ = leanh::lean_ctor_get(v_s_3834_, 6);
                v_commInst_x3f_3842_ = leanh::lean_ctor_get(v_s_3834_, 7);
                v_neutralInst_x3f_3843_ = leanh::lean_ctor_get(v_s_3834_, 8);
                v_nextId_3844_ = leanh::lean_ctor_get(v_s_3834_, 9);
                v_vars_3845_ = leanh::lean_ctor_get(v_s_3834_, 10);
                v_varMap_3846_ = leanh::lean_ctor_get(v_s_3834_, 11);
                v_denote_3847_ = leanh::lean_ctor_get(v_s_3834_, 12);
                v_denoteEntries_3848_ = leanh::lean_ctor_get(v_s_3834_, 13);
                v_queue_3849_ = leanh::lean_ctor_get(v_s_3834_, 14);
                v_basis_3850_ = leanh::lean_ctor_get(v_s_3834_, 15);
                v_diseqs_3851_ = leanh::lean_ctor_get(v_s_3834_, 16);
                v_recheck_3852_ = leanh::lean_ctor_get_uint8(
                    v_s_3834_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                );
                v_isSharedCheck_3861_ = (!leanh::lean_is_exclusive(v_s_3834_)) as u8;
                if v_isSharedCheck_3861_ == 0 {
                    v___x_3854_ = v_s_3834_;
                    v_isShared_3855_ = v_isSharedCheck_3861_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diseqs_3851_);
                    leanh::lean_inc(v_basis_3850_);
                    leanh::lean_inc(v_queue_3849_);
                    leanh::lean_inc(v_denoteEntries_3848_);
                    leanh::lean_inc(v_denote_3847_);
                    leanh::lean_inc(v_varMap_3846_);
                    leanh::lean_inc(v_vars_3845_);
                    leanh::lean_inc(v_nextId_3844_);
                    leanh::lean_inc(v_neutralInst_x3f_3843_);
                    leanh::lean_inc(v_commInst_x3f_3842_);
                    leanh::lean_inc(v_idempotentInst_x3f_3841_);
                    leanh::lean_inc(v_assocInst_3840_);
                    leanh::lean_inc(v_neutral_x3f_3839_);
                    leanh::lean_inc(v_op_3838_);
                    leanh::lean_inc(v_u_3837_);
                    leanh::lean_inc(v_type_3836_);
                    leanh::lean_inc(v_id_3835_);
                    leanh::lean_dec(v_s_3834_);
                    v___x_3854_ = leanh::lean_box(0);
                    v_isShared_3855_ = v_isSharedCheck_3861_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_e_3832_);
                v___x_3856_ = l_Lean_PersistentArray_push___redArg(v_vars_3845_, v_e_3832_);
                v___x_3857_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_varMap_3846_, v_e_3832_, v_size_3833_);
                if v_isShared_3855_ == 0 {
                    leanh::lean_ctor_set(v___x_3854_, 11, v___x_3857_);
                    leanh::lean_ctor_set(v___x_3854_, 10, v___x_3856_);
                    v___x_3859_ = v___x_3854_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_id_3835_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 1, v_type_3836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 2, v_u_3837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 3, v_op_3838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 4, v_neutral_x3f_3839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 5, v_assocInst_3840_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3860_,
                        6,
                        v_idempotentInst_x3f_3841_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 7, v_commInst_x3f_3842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 8, v_neutralInst_x3f_3843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 9, v_nextId_3844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 10, v___x_3856_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 11, v___x_3857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 12, v_denote_3847_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 13, v_denoteEntries_3848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 14, v_queue_3849_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 15, v_basis_3850_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 16, v_diseqs_3851_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3860_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                        v_recheck_3852_,
                    );
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_mkVar(
    mut v_e_3862_: *mut leanh::LeanObject,
    mut v_a_3863_: *mut leanh::LeanObject,
    mut v_a_3864_: *mut leanh::LeanObject,
    mut v_a_3865_: *mut leanh::LeanObject,
    mut v_a_3866_: *mut leanh::LeanObject,
    mut v_a_3867_: *mut leanh::LeanObject,
    mut v_a_3868_: *mut leanh::LeanObject,
    mut v_a_3869_: *mut leanh::LeanObject,
    mut v_a_3870_: *mut leanh::LeanObject,
    mut v_a_3871_: *mut leanh::LeanObject,
    mut v_a_3872_: *mut leanh::LeanObject,
    mut v_a_3873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v_vars_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3899_: u8 = 0;
    let mut v_unused_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3904_: u8 = 0;
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v_a_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3912_: u8 = 0;
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3916_: u8 = 0;
    let mut v_a_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_isSharedCheck_3925_: u8 = 0;
    let mut v_a_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3929_: u8 = 0;
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3875_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_,
                    v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_,
                );
                if leanh::lean_obj_tag(v___x_3875_) == 0 {
                    v_a_3876_ = leanh::lean_ctor_get(v___x_3875_, 0);
                    v_isSharedCheck_3925_ = (!leanh::lean_is_exclusive(v___x_3875_)) as u8;
                    if v_isSharedCheck_3925_ == 0 {
                        v___x_3878_ = v___x_3875_;
                        v_isShared_3879_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3876_);
                        leanh::lean_dec(v___x_3875_);
                        v___x_3878_ = leanh::lean_box(0);
                        v_isShared_3879_ = v_isSharedCheck_3925_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3862_);
                    v_a_3926_ = leanh::lean_ctor_get(v___x_3875_, 0);
                    v_isSharedCheck_3933_ = (!leanh::lean_is_exclusive(v___x_3875_)) as u8;
                    if v_isSharedCheck_3933_ == 0 {
                        v___x_3928_ = v___x_3875_;
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3926_);
                        leanh::lean_dec(v___x_3875_);
                        v___x_3928_ = leanh::lean_box(0);
                        v_isShared_3929_ = v_isSharedCheck_3933_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_3880_ = leanh::lean_ctor_get(v_a_3876_, 10);
                leanh::lean_inc_ref(v_vars_3880_);
                v_varMap_3881_ = leanh::lean_ctor_get(v_a_3876_, 11);
                leanh::lean_inc_ref(v_varMap_3881_);
                leanh::lean_dec(v_a_3876_);
                v___x_3882_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_varMap_3881_, v_e_3862_);
                leanh::lean_dec_ref(v_varMap_3881_);
                if leanh::lean_obj_tag(v___x_3882_) == 1 {
                    leanh::lean_dec_ref(v_vars_3880_);
                    leanh::lean_dec_ref(v_e_3862_);
                    v_val_3883_ = leanh::lean_ctor_get(v___x_3882_, 0);
                    leanh::lean_inc(v_val_3883_);
                    leanh::lean_dec_ref_known(v___x_3882_, 1);
                    if v_isShared_3879_ == 0 {
                        leanh::lean_ctor_set(v___x_3878_, 0, v_val_3883_);
                        v___x_3885_ = v___x_3878_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3886_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_val_3883_);
                        v___x_3885_ = v_reuseFailAlloc_3886_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3882_);
                    leanh::lean_del_object(v___x_3878_);
                    v_size_3887_ = leanh::lean_ctor_get(v_vars_3880_, 2);
                    leanh::lean_inc_n(v_size_3887_, 2);
                    leanh::lean_dec_ref(v_vars_3880_);
                    leanh::lean_inc_ref(v_e_3862_);
                    v___f_3888_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_AC_mkVar___lam__0 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_3888_, 0, v_e_3862_);
                    leanh::lean_closure_set(v___f_3888_, 1, v_size_3887_);
                    v___x_3889_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(
                        v___f_3888_,
                        v_a_3863_,
                        v_a_3864_,
                    );
                    if leanh::lean_obj_tag(v___x_3889_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3889_, 1);
                        leanh::lean_inc_ref(v_e_3862_);
                        v___x_3890_ = l_Lean_Meta_Grind_AC_addTermOpId___redArg(
                            v_e_3862_, v_a_3863_, v_a_3864_,
                        );
                        if leanh::lean_obj_tag(v___x_3890_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3890_, 1);
                            v___x_3891_ = l_Lean_Meta_Grind_AC_acExt;
                            v___x_3892_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                                v___x_3891_,
                                v_e_3862_,
                                v_a_3864_,
                                v_a_3865_,
                                v_a_3866_,
                                v_a_3867_,
                                v_a_3868_,
                                v_a_3869_,
                                v_a_3870_,
                                v_a_3871_,
                                v_a_3872_,
                                v_a_3873_,
                            );
                            if leanh::lean_obj_tag(v___x_3892_) == 0 {
                                v_isSharedCheck_3899_ =
                                    (!leanh::lean_is_exclusive(v___x_3892_)) as u8;
                                if v_isSharedCheck_3899_ == 0 {
                                    v_unused_3900_ = leanh::lean_ctor_get(v___x_3892_, 0);
                                    leanh::lean_dec(v_unused_3900_);
                                    v___x_3894_ = v___x_3892_;
                                    v_isShared_3895_ = v_isSharedCheck_3899_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_3892_);
                                    v___x_3894_ = leanh::lean_box(0);
                                    v_isShared_3895_ = v_isSharedCheck_3899_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_size_3887_);
                                v_a_3901_ = leanh::lean_ctor_get(v___x_3892_, 0);
                                v_isSharedCheck_3908_ =
                                    (!leanh::lean_is_exclusive(v___x_3892_)) as u8;
                                if v_isSharedCheck_3908_ == 0 {
                                    v___x_3903_ = v___x_3892_;
                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3901_);
                                    leanh::lean_dec(v___x_3892_);
                                    v___x_3903_ = leanh::lean_box(0);
                                    v_isShared_3904_ = v_isSharedCheck_3908_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_size_3887_);
                            leanh::lean_dec_ref(v_e_3862_);
                            v_a_3909_ = leanh::lean_ctor_get(v___x_3890_, 0);
                            v_isSharedCheck_3916_ =
                                (!leanh::lean_is_exclusive(v___x_3890_)) as u8;
                            if v_isSharedCheck_3916_ == 0 {
                                v___x_3911_ = v___x_3890_;
                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3909_);
                                leanh::lean_dec(v___x_3890_);
                                v___x_3911_ = leanh::lean_box(0);
                                v_isShared_3912_ = v_isSharedCheck_3916_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_size_3887_);
                        leanh::lean_dec_ref(v_e_3862_);
                        v_a_3917_ = leanh::lean_ctor_get(v___x_3889_, 0);
                        v_isSharedCheck_3924_ =
                            (!leanh::lean_is_exclusive(v___x_3889_)) as u8;
                        if v_isSharedCheck_3924_ == 0 {
                            v___x_3919_ = v___x_3889_;
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3917_);
                            leanh::lean_dec(v___x_3889_);
                            v___x_3919_ = leanh::lean_box(0);
                            v_isShared_3920_ = v_isSharedCheck_3924_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3885_;
            }
            3 => {
                if v_isShared_3895_ == 0 {
                    leanh::lean_ctor_set(v___x_3894_, 0, v_size_3887_);
                    v___x_3897_ = v___x_3894_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3898_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_size_3887_);
                    v___x_3897_ = v_reuseFailAlloc_3898_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3897_;
            }
            5 => {
                if v_isShared_3904_ == 0 {
                    v___x_3906_ = v___x_3903_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
                    v___x_3906_ = v_reuseFailAlloc_3907_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3906_;
            }
            7 => {
                if v_isShared_3912_ == 0 {
                    v___x_3914_ = v___x_3911_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3915_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
                    v___x_3914_ = v_reuseFailAlloc_3915_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3914_;
            }
            9 => {
                if v_isShared_3920_ == 0 {
                    v___x_3922_ = v___x_3919_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3923_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
                    v___x_3922_ = v_reuseFailAlloc_3923_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3922_;
            }
            11 => {
                if v_isShared_3929_ == 0 {
                    v___x_3931_ = v___x_3928_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3932_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
                    v___x_3931_ = v_reuseFailAlloc_3932_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_mkVar___boxed(
    mut v_e_3934_: *mut leanh::LeanObject,
    mut v_a_3935_: *mut leanh::LeanObject,
    mut v_a_3936_: *mut leanh::LeanObject,
    mut v_a_3937_: *mut leanh::LeanObject,
    mut v_a_3938_: *mut leanh::LeanObject,
    mut v_a_3939_: *mut leanh::LeanObject,
    mut v_a_3940_: *mut leanh::LeanObject,
    mut v_a_3941_: *mut leanh::LeanObject,
    mut v_a_3942_: *mut leanh::LeanObject,
    mut v_a_3943_: *mut leanh::LeanObject,
    mut v_a_3944_: *mut leanh::LeanObject,
    mut v_a_3945_: *mut leanh::LeanObject,
    mut v_a_3946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3947_ = l_Lean_Meta_Grind_AC_mkVar(
        v_e_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_,
        v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_,
    );
    leanh::lean_dec(v_a_3945_);
    leanh::lean_dec_ref(v_a_3944_);
    leanh::lean_dec(v_a_3943_);
    leanh::lean_dec_ref(v_a_3942_);
    leanh::lean_dec(v_a_3941_);
    leanh::lean_dec_ref(v_a_3940_);
    leanh::lean_dec(v_a_3939_);
    leanh::lean_dec_ref(v_a_3938_);
    leanh::lean_dec(v_a_3937_);
    leanh::lean_dec(v_a_3936_);
    leanh::lean_dec(v_a_3935_);
    return v_res_3947_;
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(
    mut v_e_3948_: *mut leanh::LeanObject,
    mut v___y_3949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3963_: u8 = 0;
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut v_unused_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3951_ = lean_st_ref_get(v___y_3949_);
                v_mctx_3952_ = leanh::lean_ctor_get(v___x_3951_, 0);
                leanh::lean_inc_ref(v_mctx_3952_);
                leanh::lean_dec(v___x_3951_);
                v___x_3953_ = lean_instantiate_expr_mvars(v_mctx_3952_, v_e_3948_);
                v_fst_3954_ = leanh::lean_ctor_get(v___x_3953_, 0);
                leanh::lean_inc(v_fst_3954_);
                v_snd_3955_ = leanh::lean_ctor_get(v___x_3953_, 1);
                leanh::lean_inc(v_snd_3955_);
                leanh::lean_dec_ref(v___x_3953_);
                v___x_3956_ = lean_st_ref_take(v___y_3949_);
                v_cache_3957_ = leanh::lean_ctor_get(v___x_3956_, 1);
                v_zetaDeltaFVarIds_3958_ = leanh::lean_ctor_get(v___x_3956_, 2);
                v_postponed_3959_ = leanh::lean_ctor_get(v___x_3956_, 3);
                v_diag_3960_ = leanh::lean_ctor_get(v___x_3956_, 4);
                v_isSharedCheck_3969_ = (!leanh::lean_is_exclusive(v___x_3956_)) as u8;
                if v_isSharedCheck_3969_ == 0 {
                    v_unused_3970_ = leanh::lean_ctor_get(v___x_3956_, 0);
                    leanh::lean_dec(v_unused_3970_);
                    v___x_3962_ = v___x_3956_;
                    v_isShared_3963_ = v_isSharedCheck_3969_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3960_);
                    leanh::lean_inc(v_postponed_3959_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3958_);
                    leanh::lean_inc(v_cache_3957_);
                    leanh::lean_dec(v___x_3956_);
                    v___x_3962_ = leanh::lean_box(0);
                    v_isShared_3963_ = v_isSharedCheck_3969_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3963_ == 0 {
                    leanh::lean_ctor_set(v___x_3962_, 0, v_fst_3954_);
                    v___x_3965_ = v___x_3962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3968_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_fst_3954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_cache_3957_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3968_,
                        2,
                        v_zetaDeltaFVarIds_3958_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_postponed_3959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_diag_3960_);
                    v___x_3965_ = v_reuseFailAlloc_3968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3966_ = lean_st_ref_set(v___y_3949_, v___x_3965_);
                v___x_3967_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3967_, 0, v_snd_3955_);
                return v___x_3967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg___boxed(
    mut v_e_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3974_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_3971_, v___y_3972_);
    leanh::lean_dec(v___y_3972_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(
    mut v_e_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3987_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_e_3975_, v___y_3983_);
    return v___x_3987_;
}
pub unsafe fn l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___boxed(
    mut v_e_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
    mut v___y_3990_: *mut leanh::LeanObject,
    mut v___y_3991_: *mut leanh::LeanObject,
    mut v___y_3992_: *mut leanh::LeanObject,
    mut v___y_3993_: *mut leanh::LeanObject,
    mut v___y_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
    mut v___y_3996_: *mut leanh::LeanObject,
    mut v___y_3997_: *mut leanh::LeanObject,
    mut v___y_3998_: *mut leanh::LeanObject,
    mut v___y_3999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1(v_e_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
    leanh::lean_dec(v___y_3998_);
    leanh::lean_dec_ref(v___y_3997_);
    leanh::lean_dec(v___y_3996_);
    leanh::lean_dec_ref(v___y_3995_);
    leanh::lean_dec(v___y_3994_);
    leanh::lean_dec_ref(v___y_3993_);
    leanh::lean_dec(v___y_3992_);
    leanh::lean_dec_ref(v___y_3991_);
    leanh::lean_dec(v___y_3990_);
    leanh::lean_dec(v___y_3989_);
    return v_res_4000_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4001_ = leanh::lean_unsigned_to_nat(32);
    v___x_4002_ = lean_mk_empty_array_with_capacity(v___x_4001_);
    v___x_4003_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4003_, 0, v___x_4002_);
    return v___x_4003_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4004_: usize = 0;
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4004_ = 5usize;
    v___x_4005_ = leanh::lean_unsigned_to_nat(0);
    v___x_4006_ = leanh::lean_unsigned_to_nat(32);
    v___x_4007_ = lean_mk_empty_array_with_capacity(v___x_4006_);
    v___x_4008_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__0);
    v___x_4009_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4009_, 0, v___x_4008_);
    leanh::lean_ctor_set(v___x_4009_, 1, v___x_4007_);
    leanh::lean_ctor_set(v___x_4009_, 2, v___x_4005_);
    leanh::lean_ctor_set(v___x_4009_, 3, v___x_4005_);
    leanh::lean_ctor_set_usize(v___x_4009_, 4, v___x_4004_);
    return v___x_4009_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4010_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4010_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4011_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__2);
    v___x_4012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
    return v___x_4012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(
    mut v___x_4013_: *mut leanh::LeanObject,
    mut v_binderType_4014_: *mut leanh::LeanObject,
    mut v_a_4015_: *mut leanh::LeanObject,
    mut v_op_4016_: *mut leanh::LeanObject,
    mut v_snd_4017_: *mut leanh::LeanObject,
    mut v_val_4018_: *mut leanh::LeanObject,
    mut v_a_4019_: *mut leanh::LeanObject,
    mut v_a_4020_: *mut leanh::LeanObject,
    mut v_fst_4021_: *mut leanh::LeanObject,
    mut v_a_4022_: u8,
    mut v_s_4023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4030_: u8 = 0;
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_4024_ = leanh::lean_ctor_get(v_s_4023_, 0);
                v_opIdOf_4025_ = leanh::lean_ctor_get(v_s_4023_, 1);
                v_exprToOpIds_4026_ = leanh::lean_ctor_get(v_s_4023_, 2);
                v_steps_4027_ = leanh::lean_ctor_get(v_s_4023_, 3);
                v_isSharedCheck_4041_ = (!leanh::lean_is_exclusive(v_s_4023_)) as u8;
                if v_isSharedCheck_4041_ == 0 {
                    v___x_4029_ = v_s_4023_;
                    v_isShared_4030_ = v_isSharedCheck_4041_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_4027_);
                    leanh::lean_inc(v_exprToOpIds_4026_);
                    leanh::lean_inc(v_opIdOf_4025_);
                    leanh::lean_inc(v_structs_4024_);
                    leanh::lean_dec(v_s_4023_);
                    v___x_4029_ = leanh::lean_box(0);
                    v_isShared_4030_ = v_isSharedCheck_4041_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4031_ = leanh::lean_unsigned_to_nat(0);
                v___x_4032_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__1);
                v___x_4033_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___closed__3);
                v___x_4034_ = leanh::lean_box(1);
                v___x_4035_ = leanh::lean_box(0);
                v___x_4036_ = leanh::lean_alloc_ctor(0, 17, (1) as u32);
                leanh::lean_ctor_set(v___x_4036_, 0, v___x_4013_);
                leanh::lean_ctor_set(v___x_4036_, 1, v_binderType_4014_);
                leanh::lean_ctor_set(v___x_4036_, 2, v_a_4015_);
                leanh::lean_ctor_set(v___x_4036_, 3, v_op_4016_);
                leanh::lean_ctor_set(v___x_4036_, 4, v_snd_4017_);
                leanh::lean_ctor_set(v___x_4036_, 5, v_val_4018_);
                leanh::lean_ctor_set(v___x_4036_, 6, v_a_4019_);
                leanh::lean_ctor_set(v___x_4036_, 7, v_a_4020_);
                leanh::lean_ctor_set(v___x_4036_, 8, v_fst_4021_);
                leanh::lean_ctor_set(v___x_4036_, 9, v___x_4031_);
                leanh::lean_ctor_set(v___x_4036_, 10, v___x_4032_);
                leanh::lean_ctor_set(v___x_4036_, 11, v___x_4033_);
                leanh::lean_ctor_set(v___x_4036_, 12, v___x_4033_);
                leanh::lean_ctor_set(v___x_4036_, 13, v___x_4032_);
                leanh::lean_ctor_set(v___x_4036_, 14, v___x_4034_);
                leanh::lean_ctor_set(v___x_4036_, 15, v___x_4035_);
                leanh::lean_ctor_set(v___x_4036_, 16, v___x_4032_);
                leanh::lean_ctor_set_uint8(
                    v___x_4036_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                    v_a_4022_,
                );
                v___x_4037_ = lean_array_push(v_structs_4024_, v___x_4036_);
                if v_isShared_4030_ == 0 {
                    leanh::lean_ctor_set(v___x_4029_, 0, v___x_4037_);
                    v___x_4039_ = v___x_4029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4040_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 1, v_opIdOf_4025_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 2, v_exprToOpIds_4026_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4040_, 3, v_steps_4027_);
                    v___x_4039_ = v_reuseFailAlloc_4040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed(
    mut v___x_4042_: *mut leanh::LeanObject,
    mut v_binderType_4043_: *mut leanh::LeanObject,
    mut v_a_4044_: *mut leanh::LeanObject,
    mut v_op_4045_: *mut leanh::LeanObject,
    mut v_snd_4046_: *mut leanh::LeanObject,
    mut v_val_4047_: *mut leanh::LeanObject,
    mut v_a_4048_: *mut leanh::LeanObject,
    mut v_a_4049_: *mut leanh::LeanObject,
    mut v_fst_4050_: *mut leanh::LeanObject,
    mut v_a_4051_: *mut leanh::LeanObject,
    mut v_s_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_158442__boxed_4053_: u8 = 0;
    let mut v_res_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_158442__boxed_4053_ = (leanh::lean_unbox(v_a_4051_) as u8);
    v_res_4054_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0(
            v___x_4042_,
            v_binderType_4043_,
            v_a_4044_,
            v_op_4045_,
            v_snd_4046_,
            v_val_4047_,
            v_a_4048_,
            v_a_4049_,
            v_fst_4050_,
            v_a_158442__boxed_4053_,
            v_s_4052_,
        );
    return v_res_4054_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(
    mut v_m_4055_: *mut leanh::LeanObject,
    mut v_a_4056_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4060_: u64 = 0;
    let mut v___x_4061_: u64 = 0;
    let mut v___x_4062_: u64 = 0;
    let mut v_fold_4063_: u64 = 0;
    let mut v___x_4064_: u64 = 0;
    let mut v___x_4065_: u64 = 0;
    let mut v___x_4066_: u64 = 0;
    let mut v___x_4067_: usize = 0;
    let mut v___x_4068_: usize = 0;
    let mut v___x_4069_: usize = 0;
    let mut v___x_4070_: usize = 0;
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: u64 = 0;
    let mut v_hash_4075_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4057_ = leanh::lean_ctor_get(v_m_4055_, 1);
                v___x_4058_ = lean_array_get_size(v_buckets_4057_);
                if leanh::lean_obj_tag(v_a_4056_) == 0 {
                    v___x_4074_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4060_ = v___x_4074_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4075_ = leanh::lean_ctor_get_uint64(
                        v_a_4056_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4060_ = v_hash_4075_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4061_ = 32u64;
                v___x_4062_ = lean_uint64_shift_right(v___y_4060_, v___x_4061_);
                v_fold_4063_ = lean_uint64_xor(v___y_4060_, v___x_4062_);
                v___x_4064_ = 16u64;
                v___x_4065_ = lean_uint64_shift_right(v_fold_4063_, v___x_4064_);
                v___x_4066_ = lean_uint64_xor(v_fold_4063_, v___x_4065_);
                v___x_4067_ = lean_uint64_to_usize(v___x_4066_);
                v___x_4068_ = lean_usize_of_nat(v___x_4058_);
                v___x_4069_ = 1usize;
                v___x_4070_ = lean_usize_sub(v___x_4068_, v___x_4069_);
                v___x_4071_ = lean_usize_land(v___x_4067_, v___x_4070_);
                v___x_4072_ = lean_array_uget_borrowed(v_buckets_4057_, v___x_4071_);
                v___x_4073_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc_spec__0_spec__0_spec__1___redArg(v_a_4056_, v___x_4072_);
                return v___x_4073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg___boxed(
    mut v_m_4076_: *mut leanh::LeanObject,
    mut v_a_4077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4078_: u8 = 0;
    let mut v_r_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4078_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_4076_, v_a_4077_);
    leanh::lean_dec(v_a_4077_);
    leanh::lean_dec_ref(v_m_4076_);
    v_r_4079_ = leanh::lean_box((v_res_4078_) as usize);
    return v_r_4079_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: f64 = 0.0;
    v___x_4080_ = leanh::lean_unsigned_to_nat(0);
    v___x_4081_ = lean_float_of_nat(v___x_4080_);
    return v___x_4081_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(
    mut v_cls_4085_: *mut leanh::LeanObject,
    mut v_msg_4086_: *mut leanh::LeanObject,
    mut v___y_4087_: *mut leanh::LeanObject,
    mut v___y_4088_: *mut leanh::LeanObject,
    mut v___y_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4097_: u8 = 0;
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4110_: u8 = 0;
    let mut v_tid_4111_: u64 = 0;
    let mut v_traces_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4115_: u8 = 0;
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: f64 = 0.0;
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4136_: u8 = 0;
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4092_ = leanh::lean_ctor_get(v___y_4089_, 5);
                v___x_4093_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_AC_ACM_getStruct_spec__0_spec__0(v_msg_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_);
                v_a_4094_ = leanh::lean_ctor_get(v___x_4093_, 0);
                v_isSharedCheck_4138_ = (!leanh::lean_is_exclusive(v___x_4093_)) as u8;
                if v_isSharedCheck_4138_ == 0 {
                    v___x_4096_ = v___x_4093_;
                    v_isShared_4097_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4094_);
                    leanh::lean_dec(v___x_4093_);
                    v___x_4096_ = leanh::lean_box(0);
                    v_isShared_4097_ = v_isSharedCheck_4138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4098_ = lean_st_ref_take(v___y_4090_);
                v_traceState_4099_ = leanh::lean_ctor_get(v___x_4098_, 4);
                v_env_4100_ = leanh::lean_ctor_get(v___x_4098_, 0);
                v_nextMacroScope_4101_ = leanh::lean_ctor_get(v___x_4098_, 1);
                v_ngen_4102_ = leanh::lean_ctor_get(v___x_4098_, 2);
                v_auxDeclNGen_4103_ = leanh::lean_ctor_get(v___x_4098_, 3);
                v_cache_4104_ = leanh::lean_ctor_get(v___x_4098_, 5);
                v_messages_4105_ = leanh::lean_ctor_get(v___x_4098_, 6);
                v_infoState_4106_ = leanh::lean_ctor_get(v___x_4098_, 7);
                v_snapshotTasks_4107_ = leanh::lean_ctor_get(v___x_4098_, 8);
                v_isSharedCheck_4137_ = (!leanh::lean_is_exclusive(v___x_4098_)) as u8;
                if v_isSharedCheck_4137_ == 0 {
                    v___x_4109_ = v___x_4098_;
                    v_isShared_4110_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4107_);
                    leanh::lean_inc(v_infoState_4106_);
                    leanh::lean_inc(v_messages_4105_);
                    leanh::lean_inc(v_cache_4104_);
                    leanh::lean_inc(v_traceState_4099_);
                    leanh::lean_inc(v_auxDeclNGen_4103_);
                    leanh::lean_inc(v_ngen_4102_);
                    leanh::lean_inc(v_nextMacroScope_4101_);
                    leanh::lean_inc(v_env_4100_);
                    leanh::lean_dec(v___x_4098_);
                    v___x_4109_ = leanh::lean_box(0);
                    v_isShared_4110_ = v_isSharedCheck_4137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4111_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4099_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4112_ = leanh::lean_ctor_get(v_traceState_4099_, 0);
                v_isSharedCheck_4136_ =
                    (!leanh::lean_is_exclusive(v_traceState_4099_)) as u8;
                if v_isSharedCheck_4136_ == 0 {
                    v___x_4114_ = v_traceState_4099_;
                    v_isShared_4115_ = v_isSharedCheck_4136_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4112_);
                    leanh::lean_dec(v_traceState_4099_);
                    v___x_4114_ = leanh::lean_box(0);
                    v_isShared_4115_ = v_isSharedCheck_4136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4116_ = leanh::lean_box(0);
                v___x_4117_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__0);
                v___x_4118_ = 0;
                v___x_4119_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__1;
                v___x_4120_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4120_, 0, v_cls_4085_);
                leanh::lean_ctor_set(v___x_4120_, 1, v___x_4116_);
                leanh::lean_ctor_set(v___x_4120_, 2, v___x_4119_);
                leanh::lean_ctor_set_float(
                    v___x_4120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4117_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4117_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4120_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4118_,
                );
                v___x_4121_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___closed__2;
                v___x_4122_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4122_, 0, v___x_4120_);
                leanh::lean_ctor_set(v___x_4122_, 1, v_a_4094_);
                leanh::lean_ctor_set(v___x_4122_, 2, v___x_4121_);
                leanh::lean_inc(v_ref_4092_);
                v___x_4123_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4123_, 0, v_ref_4092_);
                leanh::lean_ctor_set(v___x_4123_, 1, v___x_4122_);
                v___x_4124_ = l_Lean_PersistentArray_push___redArg(v_traces_4112_, v___x_4123_);
                if v_isShared_4115_ == 0 {
                    leanh::lean_ctor_set(v___x_4114_, 0, v___x_4124_);
                    v___x_4126_ = v___x_4114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4135_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4124_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4135_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4111_,
                    );
                    v___x_4126_ = v_reuseFailAlloc_4135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4110_ == 0 {
                    leanh::lean_ctor_set(v___x_4109_, 4, v___x_4126_);
                    v___x_4128_ = v___x_4109_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4134_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_env_4100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 1, v_nextMacroScope_4101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 2, v_ngen_4102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 3, v_auxDeclNGen_4103_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 4, v___x_4126_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 5, v_cache_4104_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 6, v_messages_4105_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 7, v_infoState_4106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4134_, 8, v_snapshotTasks_4107_);
                    v___x_4128_ = v_reuseFailAlloc_4134_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4129_ = lean_st_ref_set(v___y_4090_, v___x_4128_);
                v___x_4130_ = leanh::lean_box(0);
                if v_isShared_4097_ == 0 {
                    leanh::lean_ctor_set(v___x_4096_, 0, v___x_4130_);
                    v___x_4132_ = v___x_4096_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
                    v___x_4132_ = v_reuseFailAlloc_4133_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4132_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg___boxed(
    mut v_cls_4139_: *mut leanh::LeanObject,
    mut v_msg_4140_: *mut leanh::LeanObject,
    mut v___y_4141_: *mut leanh::LeanObject,
    mut v___y_4142_: *mut leanh::LeanObject,
    mut v___y_4143_: *mut leanh::LeanObject,
    mut v___y_4144_: *mut leanh::LeanObject,
    mut v___y_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4146_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_4139_, v_msg_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
    leanh::lean_dec(v___y_4144_);
    leanh::lean_dec_ref(v___y_4143_);
    leanh::lean_dec(v___y_4142_);
    leanh::lean_dec_ref(v___y_4141_);
    return v_res_4146_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4148_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__0;
    v___x_4149_ = l_Lean_stringToMessageData(v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4153_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__3;
    v___x_4154_ = l_Lean_MessageData_ofFormat(v___x_4153_);
    return v___x_4154_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__5;
    v___x_4157_ = l_Lean_stringToMessageData(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4172_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13;
    v___x_4173_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__15;
    v___x_4174_ = l_Lean_Name_append(v___x_4173_, v___x_4172_);
    return v___x_4174_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4176_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__17;
    v___x_4177_ = l_Lean_stringToMessageData(v___x_4176_);
    return v___x_4177_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(
    mut v_op_4195_: *mut leanh::LeanObject,
    mut v_a_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_a_4198_: *mut leanh::LeanObject,
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
    mut v_a_4201_: *mut leanh::LeanObject,
    mut v_a_4202_: *mut leanh::LeanObject,
    mut v_a_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
    mut v_a_4205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut v___y_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut v___y_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4310_: u8 = 0;
    let mut v___y_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4338_: u8 = 0;
    let mut v_inheritedTraceOptions_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: u8 = 0;
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_a_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4363_: u8 = 0;
    let mut v_f_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v_binderType_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4390_: u8 = 0;
    let mut v_binderType_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4398_: u8 = 0;
    let mut v___x_4399_: u8 = 0;
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4408_: u8 = 0;
    let mut v___x_4409_: u8 = 0;
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4419_: u8 = 0;
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v_val_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4435_: u8 = 0;
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: u8 = 0;
    let mut v_reuseFailAlloc_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4475_: u8 = 0;
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_a_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_a_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: u8 = 0;
    let mut v_a_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4502_: u8 = 0;
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut v_a_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_reuseFailAlloc_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4523_: u8 = 0;
    let mut v_a_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4531_: u8 = 0;
    let mut v_isSharedCheck_4532_: u8 = 0;
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v_a_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut v_a_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4549_: u8 = 0;
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4553_: u8 = 0;
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_a_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4566_: u8 = 0;
    let mut v_isSharedCheck_4567_: u8 = 0;
    let mut v_a_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4593_: u8 = 0;
    let mut v_a_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4597_: u8 = 0;
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4601_: u8 = 0;
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut v_a_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_declName_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_f_4364_ = l_Lean_Expr_getAppFn(v_op_4195_);
                if leanh::lean_obj_tag(v_f_4364_) == 4 {
                    v_declName_4627_ = leanh::lean_ctor_get(v_f_4364_, 0);
                    leanh::lean_inc(v_declName_4627_);
                    v___x_4628_ =
                        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc;
                    v___x_4629_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v___x_4628_, v_declName_4627_);
                    leanh::lean_dec(v_declName_4627_);
                    if v___x_4629_ == 0 {
                        v___y_4366_ = v_a_4196_;
                        v___y_4367_ = v_a_4197_;
                        v___y_4368_ = v_a_4198_;
                        v___y_4369_ = v_a_4199_;
                        v___y_4370_ = v_a_4200_;
                        v___y_4371_ = v_a_4201_;
                        v___y_4372_ = v_a_4202_;
                        v___y_4373_ = v_a_4203_;
                        v___y_4374_ = v_a_4204_;
                        v___y_4375_ = v_a_4205_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_f_4364_, 2);
                        leanh::lean_dec_ref(v_op_4195_);
                        v___x_4630_ = leanh::lean_box(0);
                        v___x_4631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4631_, 0, v___x_4630_);
                        return v___x_4631_;
                    }
                } else {
                    v___y_4366_ = v_a_4196_;
                    v___y_4367_ = v_a_4197_;
                    v___y_4368_ = v_a_4198_;
                    v___y_4369_ = v_a_4199_;
                    v___y_4370_ = v_a_4200_;
                    v___y_4371_ = v_a_4201_;
                    v___y_4372_ = v_a_4202_;
                    v___y_4373_ = v_a_4203_;
                    v___y_4374_ = v_a_4204_;
                    v___y_4375_ = v_a_4205_;
                    state = 15;
                    continue;
                }
            }
            1 => {
                v___x_4209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4209_, 0, v___y_4208_);
                v___x_4210_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4210_, 0, v___x_4209_);
                return v___x_4210_;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_4213_) == 1 {
                    v_val_4224_ = leanh::lean_ctor_get(v___y_4213_, 0);
                    leanh::lean_inc(v_val_4224_);
                    leanh::lean_dec_ref_known(v___y_4213_, 1);
                    v___x_4225_ = l_Lean_Meta_Grind_AC_mkVar(
                        v_val_4224_,
                        v___y_4212_,
                        v___y_4214_,
                        v___y_4215_,
                        v___y_4216_,
                        v___y_4217_,
                        v___y_4218_,
                        v___y_4219_,
                        v___y_4220_,
                        v___y_4221_,
                        v___y_4222_,
                        v___y_4223_,
                    );
                    if leanh::lean_obj_tag(v___x_4225_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4225_, 1);
                        v___y_4208_ = v___y_4212_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_4212_);
                        v_a_4226_ = leanh::lean_ctor_get(v___x_4225_, 0);
                        v_isSharedCheck_4233_ =
                            (!leanh::lean_is_exclusive(v___x_4225_)) as u8;
                        if v_isSharedCheck_4233_ == 0 {
                            v___x_4228_ = v___x_4225_;
                            v_isShared_4229_ = v_isSharedCheck_4233_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4226_);
                            leanh::lean_dec(v___x_4225_);
                            v___x_4228_ = leanh::lean_box(0);
                            v_isShared_4229_ = v_isSharedCheck_4233_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_4213_);
                    v___y_4208_ = v___y_4212_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4229_ == 0 {
                    v___x_4231_ = v___x_4228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
                    v___x_4231_ = v_reuseFailAlloc_4232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4231_;
            }
            5 => {
                v___x_4250_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4250_, 0, v___y_4246_);
                leanh::lean_ctor_set(v___x_4250_, 1, v___y_4249_);
                leanh::lean_inc(v___y_4239_);
                v___x_4251_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v___y_4239_, v___x_4250_, v___y_4241_, v___y_4243_, v___y_4248_, v___y_4236_);
                if leanh::lean_obj_tag(v___x_4251_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4251_, 1);
                    v___y_4212_ = v___y_4237_;
                    v___y_4213_ = v___y_4238_;
                    v___y_4214_ = v___y_4235_;
                    v___y_4215_ = v___y_4242_;
                    v___y_4216_ = v___y_4247_;
                    v___y_4217_ = v___y_4244_;
                    v___y_4218_ = v___y_4240_;
                    v___y_4219_ = v___y_4245_;
                    v___y_4220_ = v___y_4241_;
                    v___y_4221_ = v___y_4243_;
                    v___y_4222_ = v___y_4248_;
                    v___y_4223_ = v___y_4236_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4238_);
                    leanh::lean_dec(v___y_4237_);
                    v_a_4252_ = leanh::lean_ctor_get(v___x_4251_, 0);
                    v_isSharedCheck_4259_ = (!leanh::lean_is_exclusive(v___x_4251_)) as u8;
                    if v_isSharedCheck_4259_ == 0 {
                        v___x_4254_ = v___x_4251_;
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4252_);
                        leanh::lean_dec(v___x_4251_);
                        v___x_4254_ = leanh::lean_box(0);
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4255_ == 0 {
                    v___x_4257_ = v___x_4254_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4257_;
            }
            8 => {
                leanh::lean_inc_ref(v___y_4275_);
                v___x_4276_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4276_, 0, v___y_4275_);
                v___x_4277_ = l_Lean_MessageData_ofFormat(v___x_4276_);
                v___x_4278_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4278_, 0, v___y_4262_);
                leanh::lean_ctor_set(v___x_4278_, 1, v___x_4277_);
                v___x_4279_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__1);
                v___x_4280_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4280_, 0, v___x_4278_);
                leanh::lean_ctor_set(v___x_4280_, 1, v___x_4279_);
                if leanh::lean_obj_tag(v___y_4265_) == 0 {
                    v___x_4281_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__4);
                    v___y_4235_ = v___y_4261_;
                    v___y_4236_ = v___y_4263_;
                    v___y_4237_ = v___y_4264_;
                    v___y_4238_ = v___y_4265_;
                    v___y_4239_ = v___y_4266_;
                    v___y_4240_ = v___y_4267_;
                    v___y_4241_ = v___y_4268_;
                    v___y_4242_ = v___y_4269_;
                    v___y_4243_ = v___y_4270_;
                    v___y_4244_ = v___y_4271_;
                    v___y_4245_ = v___y_4272_;
                    v___y_4246_ = v___x_4280_;
                    v___y_4247_ = v___y_4273_;
                    v___y_4248_ = v___y_4274_;
                    v___y_4249_ = v___x_4281_;
                    state = 5;
                    continue;
                } else {
                    v_val_4282_ = leanh::lean_ctor_get(v___y_4265_, 0);
                    leanh::lean_inc(v_val_4282_);
                    v___x_4283_ = l_Lean_MessageData_ofExpr(v_val_4282_);
                    v___y_4235_ = v___y_4261_;
                    v___y_4236_ = v___y_4263_;
                    v___y_4237_ = v___y_4264_;
                    v___y_4238_ = v___y_4265_;
                    v___y_4239_ = v___y_4266_;
                    v___y_4240_ = v___y_4267_;
                    v___y_4241_ = v___y_4268_;
                    v___y_4242_ = v___y_4269_;
                    v___y_4243_ = v___y_4270_;
                    v___y_4244_ = v___y_4271_;
                    v___y_4245_ = v___y_4272_;
                    v___y_4246_ = v___x_4280_;
                    v___y_4247_ = v___y_4273_;
                    v___y_4248_ = v___y_4274_;
                    v___y_4249_ = v___x_4283_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                leanh::lean_inc_ref(v___y_4300_);
                v___x_4301_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4301_, 0, v___y_4300_);
                v___x_4302_ = l_Lean_MessageData_ofFormat(v___x_4301_);
                v___x_4303_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4303_, 0, v___y_4285_);
                leanh::lean_ctor_set(v___x_4303_, 1, v___x_4302_);
                v___x_4304_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__6);
                v___x_4305_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4305_, 0, v___x_4303_);
                leanh::lean_ctor_set(v___x_4305_, 1, v___x_4304_);
                if leanh::lean_obj_tag(v___y_4288_) == 0 {
                    v___x_4306_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7;
                    v___y_4261_ = v___y_4286_;
                    v___y_4262_ = v___x_4305_;
                    v___y_4263_ = v___y_4287_;
                    v___y_4264_ = v___y_4289_;
                    v___y_4265_ = v___y_4290_;
                    v___y_4266_ = v___y_4291_;
                    v___y_4267_ = v___y_4292_;
                    v___y_4268_ = v___y_4293_;
                    v___y_4269_ = v___y_4294_;
                    v___y_4270_ = v___y_4295_;
                    v___y_4271_ = v___y_4296_;
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4298_;
                    v___y_4274_ = v___y_4299_;
                    v___y_4275_ = v___x_4306_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___y_4288_, 1);
                    v___x_4307_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8;
                    v___y_4261_ = v___y_4286_;
                    v___y_4262_ = v___x_4305_;
                    v___y_4263_ = v___y_4287_;
                    v___y_4264_ = v___y_4289_;
                    v___y_4265_ = v___y_4290_;
                    v___y_4266_ = v___y_4291_;
                    v___y_4267_ = v___y_4292_;
                    v___y_4268_ = v___y_4293_;
                    v___y_4269_ = v___y_4294_;
                    v___y_4270_ = v___y_4295_;
                    v___y_4271_ = v___y_4296_;
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4298_;
                    v___y_4274_ = v___y_4299_;
                    v___y_4275_ = v___x_4307_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_4329_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v___y_4319_, v___y_4327_);
                if leanh::lean_obj_tag(v___x_4329_) == 0 {
                    v_a_4330_ = leanh::lean_ctor_get(v___x_4329_, 0);
                    leanh::lean_inc(v_a_4330_);
                    leanh::lean_dec_ref_known(v___x_4329_, 1);
                    v_structs_4331_ = leanh::lean_ctor_get(v_a_4330_, 0);
                    leanh::lean_inc_ref(v_structs_4331_);
                    leanh::lean_dec(v_a_4330_);
                    v___x_4332_ = lean_array_get_size(v_structs_4331_);
                    leanh::lean_dec_ref(v_structs_4331_);
                    v___x_4333_ = leanh::lean_box((v___y_4310_) as usize);
                    leanh::lean_inc(v_snd_4318_);
                    leanh::lean_inc_ref(v_op_4195_);
                    v___f_4334_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___lam__0___boxed as *mut core::ffi::c_void, 11, 10);
                    leanh::lean_closure_set(v___f_4334_, 0, v___x_4332_);
                    leanh::lean_closure_set(v___f_4334_, 1, v___y_4311_);
                    leanh::lean_closure_set(v___f_4334_, 2, v___y_4314_);
                    leanh::lean_closure_set(v___f_4334_, 3, v_op_4195_);
                    leanh::lean_closure_set(v___f_4334_, 4, v_snd_4318_);
                    leanh::lean_closure_set(v___f_4334_, 5, v___y_4309_);
                    leanh::lean_closure_set(v___f_4334_, 6, v___y_4312_);
                    leanh::lean_closure_set(v___f_4334_, 7, v___y_4313_);
                    leanh::lean_closure_set(v___f_4334_, 8, v_fst_4317_);
                    leanh::lean_closure_set(v___f_4334_, 9, v___x_4333_);
                    v___x_4335_ = l_Lean_Meta_Grind_AC_acExt;
                    v___x_4336_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4335_, v___f_4334_, v___y_4319_);
                    if leanh::lean_obj_tag(v___x_4336_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4336_, 1);
                        v_options_4337_ = leanh::lean_ctor_get(v___y_4327_, 2);
                        v_hasTrace_4338_ = leanh::lean_ctor_get_uint8(
                            v_options_4337_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_4338_ == 0 {
                            leanh::lean_dec(v___y_4316_);
                            leanh::lean_dec(v___y_4315_);
                            leanh::lean_dec_ref(v_op_4195_);
                            v___y_4212_ = v___x_4332_;
                            v___y_4213_ = v_snd_4318_;
                            v___y_4214_ = v___y_4319_;
                            v___y_4215_ = v___y_4320_;
                            v___y_4216_ = v___y_4321_;
                            v___y_4217_ = v___y_4322_;
                            v___y_4218_ = v___y_4323_;
                            v___y_4219_ = v___y_4324_;
                            v___y_4220_ = v___y_4325_;
                            v___y_4221_ = v___y_4326_;
                            v___y_4222_ = v___y_4327_;
                            v___y_4223_ = v___y_4328_;
                            state = 2;
                            continue;
                        } else {
                            v_inheritedTraceOptions_4339_ =
                                leanh::lean_ctor_get(v___y_4327_, 13);
                            v___x_4340_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__13;
                            v___x_4341_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__16);
                            v___x_4342_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_4339_,
                                v_options_4337_,
                                v___x_4341_,
                            );
                            if v___x_4342_ == 0 {
                                leanh::lean_dec(v___y_4316_);
                                leanh::lean_dec(v___y_4315_);
                                leanh::lean_dec_ref(v_op_4195_);
                                v___y_4212_ = v___x_4332_;
                                v___y_4213_ = v_snd_4318_;
                                v___y_4214_ = v___y_4319_;
                                v___y_4215_ = v___y_4320_;
                                v___y_4216_ = v___y_4321_;
                                v___y_4217_ = v___y_4322_;
                                v___y_4218_ = v___y_4323_;
                                v___y_4219_ = v___y_4324_;
                                v___y_4220_ = v___y_4325_;
                                v___y_4221_ = v___y_4326_;
                                v___y_4222_ = v___y_4327_;
                                v___y_4223_ = v___y_4328_;
                                state = 2;
                                continue;
                            } else {
                                v___x_4343_ = l_Lean_MessageData_ofExpr(v_op_4195_);
                                v___x_4344_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18_once), _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__18);
                                v___x_4345_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4345_, 0, v___x_4343_);
                                leanh::lean_ctor_set(v___x_4345_, 1, v___x_4344_);
                                if leanh::lean_obj_tag(v___y_4316_) == 0 {
                                    v___x_4346_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__7;
                                    v___y_4285_ = v___x_4345_;
                                    v___y_4286_ = v___y_4319_;
                                    v___y_4287_ = v___y_4328_;
                                    v___y_4288_ = v___y_4315_;
                                    v___y_4289_ = v___x_4332_;
                                    v___y_4290_ = v_snd_4318_;
                                    v___y_4291_ = v___x_4340_;
                                    v___y_4292_ = v___y_4323_;
                                    v___y_4293_ = v___y_4325_;
                                    v___y_4294_ = v___y_4320_;
                                    v___y_4295_ = v___y_4326_;
                                    v___y_4296_ = v___y_4322_;
                                    v___y_4297_ = v___y_4324_;
                                    v___y_4298_ = v___y_4321_;
                                    v___y_4299_ = v___y_4327_;
                                    v___y_4300_ = v___x_4346_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref_known(v___y_4316_, 1);
                                    v___x_4347_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__8;
                                    v___y_4285_ = v___x_4345_;
                                    v___y_4286_ = v___y_4319_;
                                    v___y_4287_ = v___y_4328_;
                                    v___y_4288_ = v___y_4315_;
                                    v___y_4289_ = v___x_4332_;
                                    v___y_4290_ = v_snd_4318_;
                                    v___y_4291_ = v___x_4340_;
                                    v___y_4292_ = v___y_4323_;
                                    v___y_4293_ = v___y_4325_;
                                    v___y_4294_ = v___y_4320_;
                                    v___y_4295_ = v___y_4326_;
                                    v___y_4296_ = v___y_4322_;
                                    v___y_4297_ = v___y_4324_;
                                    v___y_4298_ = v___y_4321_;
                                    v___y_4299_ = v___y_4327_;
                                    v___y_4300_ = v___x_4347_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_snd_4318_);
                        leanh::lean_dec(v___y_4316_);
                        leanh::lean_dec(v___y_4315_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4348_ = leanh::lean_ctor_get(v___x_4336_, 0);
                        v_isSharedCheck_4355_ =
                            (!leanh::lean_is_exclusive(v___x_4336_)) as u8;
                        if v_isSharedCheck_4355_ == 0 {
                            v___x_4350_ = v___x_4336_;
                            v_isShared_4351_ = v_isSharedCheck_4355_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4348_);
                            leanh::lean_dec(v___x_4336_);
                            v___x_4350_ = leanh::lean_box(0);
                            v_isShared_4351_ = v_isSharedCheck_4355_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_4318_);
                    leanh::lean_dec(v_fst_4317_);
                    leanh::lean_dec(v___y_4316_);
                    leanh::lean_dec(v___y_4315_);
                    leanh::lean_dec(v___y_4314_);
                    leanh::lean_dec(v___y_4313_);
                    leanh::lean_dec(v___y_4312_);
                    leanh::lean_dec_ref(v___y_4311_);
                    leanh::lean_dec_ref(v___y_4309_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v_a_4356_ = leanh::lean_ctor_get(v___x_4329_, 0);
                    v_isSharedCheck_4363_ = (!leanh::lean_is_exclusive(v___x_4329_)) as u8;
                    if v_isSharedCheck_4363_ == 0 {
                        v___x_4358_ = v___x_4329_;
                        v_isShared_4359_ = v_isSharedCheck_4363_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4356_);
                        leanh::lean_dec(v___x_4329_);
                        v___x_4358_ = leanh::lean_box(0);
                        v_isShared_4359_ = v_isSharedCheck_4363_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4351_ == 0 {
                    v___x_4353_ = v___x_4350_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4353_;
            }
            13 => {
                if v_isShared_4359_ == 0 {
                    v___x_4361_ = v___x_4358_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
                    v___x_4361_ = v_reuseFailAlloc_4362_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4361_;
            }
            15 => {
                leanh::lean_inc(v___y_4375_);
                leanh::lean_inc_ref(v___y_4374_);
                leanh::lean_inc(v___y_4373_);
                leanh::lean_inc_ref(v___y_4372_);
                leanh::lean_inc_ref(v_op_4195_);
                v___x_4376_ = lean_infer_type(
                    v_op_4195_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if leanh::lean_obj_tag(v___x_4376_) == 0 {
                    v_a_4377_ = leanh::lean_ctor_get(v___x_4376_, 0);
                    leanh::lean_inc(v_a_4377_);
                    leanh::lean_dec_ref_known(v___x_4376_, 1);
                    leanh::lean_inc(v___y_4375_);
                    leanh::lean_inc_ref(v___y_4374_);
                    leanh::lean_inc(v___y_4373_);
                    leanh::lean_inc_ref(v___y_4372_);
                    v___x_4378_ = lean_whnf(
                        v_a_4377_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if leanh::lean_obj_tag(v___x_4378_) == 0 {
                        v_a_4379_ = leanh::lean_ctor_get(v___x_4378_, 0);
                        v_isSharedCheck_4610_ =
                            (!leanh::lean_is_exclusive(v___x_4378_)) as u8;
                        if v_isSharedCheck_4610_ == 0 {
                            v___x_4381_ = v___x_4378_;
                            v_isShared_4382_ = v_isSharedCheck_4610_;
                            state = 16;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4379_);
                            leanh::lean_dec(v___x_4378_);
                            v___x_4381_ = leanh::lean_box(0);
                            v_isShared_4382_ = v_isSharedCheck_4610_;
                            state = 16;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_f_4364_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4611_ = leanh::lean_ctor_get(v___x_4378_, 0);
                        v_isSharedCheck_4618_ =
                            (!leanh::lean_is_exclusive(v___x_4378_)) as u8;
                        if v_isSharedCheck_4618_ == 0 {
                            v___x_4613_ = v___x_4378_;
                            v_isShared_4614_ = v_isSharedCheck_4618_;
                            state = 60;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4611_);
                            leanh::lean_dec(v___x_4378_);
                            v___x_4613_ = leanh::lean_box(0);
                            v_isShared_4614_ = v_isSharedCheck_4618_;
                            state = 60;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_4364_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v_a_4619_ = leanh::lean_ctor_get(v___x_4376_, 0);
                    v_isSharedCheck_4626_ = (!leanh::lean_is_exclusive(v___x_4376_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4376_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 62;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4619_);
                        leanh::lean_dec(v___x_4376_);
                        v___x_4621_ = leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 62;
                        continue;
                    }
                }
            }
            16 => {
                if leanh::lean_obj_tag(v_a_4379_) == 7 {
                    v_binderType_4383_ = leanh::lean_ctor_get(v_a_4379_, 1);
                    leanh::lean_inc_ref(v_binderType_4383_);
                    v_body_4384_ = leanh::lean_ctor_get(v_a_4379_, 2);
                    leanh::lean_inc_ref(v_body_4384_);
                    leanh::lean_dec_ref_known(v_a_4379_, 3);
                    v___x_4385_ = l_Lean_Expr_hasLooseBVars(v_body_4384_);
                    if v___x_4385_ == 0 {
                        leanh::lean_del_object(v___x_4381_);
                        leanh::lean_inc(v___y_4375_);
                        leanh::lean_inc_ref(v___y_4374_);
                        leanh::lean_inc(v___y_4373_);
                        leanh::lean_inc_ref(v___y_4372_);
                        v___x_4386_ = lean_whnf(
                            v_body_4384_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if leanh::lean_obj_tag(v___x_4386_) == 0 {
                            v_a_4387_ = leanh::lean_ctor_get(v___x_4386_, 0);
                            v_isSharedCheck_4593_ =
                                (!leanh::lean_is_exclusive(v___x_4386_)) as u8;
                            if v_isSharedCheck_4593_ == 0 {
                                v___x_4389_ = v___x_4386_;
                                v_isShared_4390_ = v_isSharedCheck_4593_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4387_);
                                leanh::lean_dec(v___x_4386_);
                                v___x_4389_ = leanh::lean_box(0);
                                v_isShared_4390_ = v_isSharedCheck_4593_;
                                state = 17;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_binderType_4383_);
                            leanh::lean_dec_ref(v_f_4364_);
                            leanh::lean_dec_ref(v_op_4195_);
                            v_a_4594_ = leanh::lean_ctor_get(v___x_4386_, 0);
                            v_isSharedCheck_4601_ =
                                (!leanh::lean_is_exclusive(v___x_4386_)) as u8;
                            if v_isSharedCheck_4601_ == 0 {
                                v___x_4596_ = v___x_4386_;
                                v_isShared_4597_ = v_isSharedCheck_4601_;
                                state = 56;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4594_);
                                leanh::lean_dec(v___x_4386_);
                                v___x_4596_ = leanh::lean_box(0);
                                v_isShared_4597_ = v_isSharedCheck_4601_;
                                state = 56;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_4384_);
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_f_4364_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v___x_4602_ = leanh::lean_box(0);
                        if v_isShared_4382_ == 0 {
                            leanh::lean_ctor_set(v___x_4381_, 0, v___x_4602_);
                            v___x_4604_ = v___x_4381_;
                            state = 58;
                            continue;
                        } else {
                            v_reuseFailAlloc_4605_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v___x_4602_);
                            v___x_4604_ = v_reuseFailAlloc_4605_;
                            state = 58;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4379_);
                    leanh::lean_dec_ref(v_f_4364_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v___x_4606_ = leanh::lean_box(0);
                    if v_isShared_4382_ == 0 {
                        leanh::lean_ctor_set(v___x_4381_, 0, v___x_4606_);
                        v___x_4608_ = v___x_4381_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_4609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
                        v___x_4608_ = v_reuseFailAlloc_4609_;
                        state = 59;
                        continue;
                    }
                }
            }
            17 => {
                if leanh::lean_obj_tag(v_a_4387_) == 7 {
                    v_binderType_4391_ = leanh::lean_ctor_get(v_a_4387_, 1);
                    leanh::lean_inc_ref(v_binderType_4391_);
                    v_body_4392_ = leanh::lean_ctor_get(v_a_4387_, 2);
                    leanh::lean_inc_ref(v_body_4392_);
                    leanh::lean_dec_ref_known(v_a_4387_, 3);
                    v___x_4393_ = l_Lean_Expr_hasLooseBVars(v_body_4392_);
                    if v___x_4393_ == 0 {
                        leanh::lean_del_object(v___x_4389_);
                        leanh::lean_inc_ref(v_binderType_4383_);
                        v___x_4394_ = l_Lean_Meta_isExprDefEq(
                            v_binderType_4383_,
                            v_binderType_4391_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if leanh::lean_obj_tag(v___x_4394_) == 0 {
                            v_a_4395_ = leanh::lean_ctor_get(v___x_4394_, 0);
                            v_isSharedCheck_4576_ =
                                (!leanh::lean_is_exclusive(v___x_4394_)) as u8;
                            if v_isSharedCheck_4576_ == 0 {
                                v___x_4397_ = v___x_4394_;
                                v_isShared_4398_ = v_isSharedCheck_4576_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4395_);
                                leanh::lean_dec(v___x_4394_);
                                v___x_4397_ = leanh::lean_box(0);
                                v_isShared_4398_ = v_isSharedCheck_4576_;
                                state = 18;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_body_4392_);
                            leanh::lean_dec_ref(v_binderType_4383_);
                            leanh::lean_dec_ref(v_f_4364_);
                            leanh::lean_dec_ref(v_op_4195_);
                            v_a_4577_ = leanh::lean_ctor_get(v___x_4394_, 0);
                            v_isSharedCheck_4584_ =
                                (!leanh::lean_is_exclusive(v___x_4394_)) as u8;
                            if v_isSharedCheck_4584_ == 0 {
                                v___x_4579_ = v___x_4394_;
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 52;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4577_);
                                leanh::lean_dec(v___x_4394_);
                                v___x_4579_ = leanh::lean_box(0);
                                v_isShared_4580_ = v_isSharedCheck_4584_;
                                state = 52;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_4392_);
                        leanh::lean_dec_ref(v_binderType_4391_);
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_f_4364_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v___x_4585_ = leanh::lean_box(0);
                        if v_isShared_4390_ == 0 {
                            leanh::lean_ctor_set(v___x_4389_, 0, v___x_4585_);
                            v___x_4587_ = v___x_4389_;
                            state = 54;
                            continue;
                        } else {
                            v_reuseFailAlloc_4588_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4588_, 0, v___x_4585_);
                            v___x_4587_ = v_reuseFailAlloc_4588_;
                            state = 54;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4387_);
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_f_4364_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v___x_4589_ = leanh::lean_box(0);
                    if v_isShared_4390_ == 0 {
                        leanh::lean_ctor_set(v___x_4389_, 0, v___x_4589_);
                        v___x_4591_ = v___x_4389_;
                        state = 55;
                        continue;
                    } else {
                        v_reuseFailAlloc_4592_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4589_);
                        v___x_4591_ = v_reuseFailAlloc_4592_;
                        state = 55;
                        continue;
                    }
                }
            }
            18 => {
                v___x_4399_ = (leanh::lean_unbox(v_a_4395_) as u8);
                leanh::lean_dec(v_a_4395_);
                if v___x_4399_ == 0 {
                    leanh::lean_dec_ref(v_body_4392_);
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_f_4364_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v___x_4400_ = leanh::lean_box(0);
                    if v_isShared_4398_ == 0 {
                        leanh::lean_ctor_set(v___x_4397_, 0, v___x_4400_);
                        v___x_4402_ = v___x_4397_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_4403_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
                        v___x_4402_ = v_reuseFailAlloc_4403_;
                        state = 19;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4397_);
                    leanh::lean_inc_ref(v_binderType_4383_);
                    v___x_4404_ = l_Lean_Meta_isExprDefEq(
                        v_binderType_4383_,
                        v_body_4392_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if leanh::lean_obj_tag(v___x_4404_) == 0 {
                        v_a_4405_ = leanh::lean_ctor_get(v___x_4404_, 0);
                        v_isSharedCheck_4567_ =
                            (!leanh::lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4567_ == 0 {
                            v___x_4407_ = v___x_4404_;
                            v_isShared_4408_ = v_isSharedCheck_4567_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4405_);
                            leanh::lean_dec(v___x_4404_);
                            v___x_4407_ = leanh::lean_box(0);
                            v_isShared_4408_ = v_isSharedCheck_4567_;
                            state = 20;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_f_4364_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4568_ = leanh::lean_ctor_get(v___x_4404_, 0);
                        v_isSharedCheck_4575_ =
                            (!leanh::lean_is_exclusive(v___x_4404_)) as u8;
                        if v_isSharedCheck_4575_ == 0 {
                            v___x_4570_ = v___x_4404_;
                            v_isShared_4571_ = v_isSharedCheck_4575_;
                            state = 50;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4568_);
                            leanh::lean_dec(v___x_4404_);
                            v___x_4570_ = leanh::lean_box(0);
                            v_isShared_4571_ = v_isSharedCheck_4575_;
                            state = 50;
                            continue;
                        }
                    }
                }
            }
            19 => {
                return v___x_4402_;
            }
            20 => {
                v___x_4409_ = (leanh::lean_unbox(v_a_4405_) as u8);
                leanh::lean_dec(v_a_4405_);
                if v___x_4409_ == 0 {
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_f_4364_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v___x_4410_ = leanh::lean_box(0);
                    if v_isShared_4408_ == 0 {
                        leanh::lean_ctor_set(v___x_4407_, 0, v___x_4410_);
                        v___x_4412_ = v___x_4407_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_4413_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4410_);
                        v___x_4412_ = v_reuseFailAlloc_4413_;
                        state = 21;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4407_);
                    v___x_4414_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_isArithOpInOtherModules(v_op_4195_, v_f_4364_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
                    leanh::lean_dec_ref(v_f_4364_);
                    if leanh::lean_obj_tag(v___x_4414_) == 0 {
                        v_a_4415_ = leanh::lean_ctor_get(v___x_4414_, 0);
                        v_isSharedCheck_4558_ =
                            (!leanh::lean_is_exclusive(v___x_4414_)) as u8;
                        if v_isSharedCheck_4558_ == 0 {
                            v___x_4417_ = v___x_4414_;
                            v_isShared_4418_ = v_isSharedCheck_4558_;
                            state = 22;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4415_);
                            leanh::lean_dec(v___x_4414_);
                            v___x_4417_ = leanh::lean_box(0);
                            v_isShared_4418_ = v_isSharedCheck_4558_;
                            state = 22;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4559_ = leanh::lean_ctor_get(v___x_4414_, 0);
                        v_isSharedCheck_4566_ =
                            (!leanh::lean_is_exclusive(v___x_4414_)) as u8;
                        if v_isSharedCheck_4566_ == 0 {
                            v___x_4561_ = v___x_4414_;
                            v_isShared_4562_ = v_isSharedCheck_4566_;
                            state = 48;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4559_);
                            leanh::lean_dec(v___x_4414_);
                            v___x_4561_ = leanh::lean_box(0);
                            v_isShared_4562_ = v_isSharedCheck_4566_;
                            state = 48;
                            continue;
                        }
                    }
                }
            }
            21 => {
                return v___x_4412_;
            }
            22 => {
                v___x_4419_ = (leanh::lean_unbox(v_a_4415_) as u8);
                if v___x_4419_ == 0 {
                    leanh::lean_del_object(v___x_4417_);
                    leanh::lean_inc_ref(v_binderType_4383_);
                    v___x_4420_ = l_Lean_Meta_getLevel(
                        v_binderType_4383_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if leanh::lean_obj_tag(v___x_4420_) == 0 {
                        v_a_4421_ = leanh::lean_ctor_get(v___x_4420_, 0);
                        leanh::lean_inc_n(v_a_4421_, 2);
                        leanh::lean_dec_ref_known(v___x_4420_, 1);
                        v___x_4422_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__21;
                        v___x_4423_ = leanh::lean_box(0);
                        v___x_4424_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4424_, 0, v_a_4421_);
                        leanh::lean_ctor_set(v___x_4424_, 1, v___x_4423_);
                        leanh::lean_inc_ref(v___x_4424_);
                        v___x_4425_ = l_Lean_mkConst(v___x_4422_, v___x_4424_);
                        leanh::lean_inc_ref(v_op_4195_);
                        leanh::lean_inc_ref(v_binderType_4383_);
                        v___x_4426_ = l_Lean_mkAppB(v___x_4425_, v_binderType_4383_, v_op_4195_);
                        v___x_4427_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                            v___x_4426_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if leanh::lean_obj_tag(v___x_4427_) == 0 {
                            v_a_4428_ = leanh::lean_ctor_get(v___x_4427_, 0);
                            v_isSharedCheck_4537_ =
                                (!leanh::lean_is_exclusive(v___x_4427_)) as u8;
                            if v_isSharedCheck_4537_ == 0 {
                                v___x_4430_ = v___x_4427_;
                                v_isShared_4431_ = v_isSharedCheck_4537_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4428_);
                                leanh::lean_dec(v___x_4427_);
                                v___x_4430_ = leanh::lean_box(0);
                                v_isShared_4431_ = v_isSharedCheck_4537_;
                                state = 23;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_4424_, 2);
                            leanh::lean_dec(v_a_4421_);
                            leanh::lean_dec(v_a_4415_);
                            leanh::lean_dec_ref(v_binderType_4383_);
                            leanh::lean_dec_ref(v_op_4195_);
                            v_a_4538_ = leanh::lean_ctor_get(v___x_4427_, 0);
                            v_isSharedCheck_4545_ =
                                (!leanh::lean_is_exclusive(v___x_4427_)) as u8;
                            if v_isSharedCheck_4545_ == 0 {
                                v___x_4540_ = v___x_4427_;
                                v_isShared_4541_ = v_isSharedCheck_4545_;
                                state = 43;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4538_);
                                leanh::lean_dec(v___x_4427_);
                                v___x_4540_ = leanh::lean_box(0);
                                v_isShared_4541_ = v_isSharedCheck_4545_;
                                state = 43;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4415_);
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4546_ = leanh::lean_ctor_get(v___x_4420_, 0);
                        v_isSharedCheck_4553_ =
                            (!leanh::lean_is_exclusive(v___x_4420_)) as u8;
                        if v_isSharedCheck_4553_ == 0 {
                            v___x_4548_ = v___x_4420_;
                            v_isShared_4549_ = v_isSharedCheck_4553_;
                            state = 45;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4546_);
                            leanh::lean_dec(v___x_4420_);
                            v___x_4548_ = leanh::lean_box(0);
                            v_isShared_4549_ = v_isSharedCheck_4553_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4415_);
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v___x_4554_ = leanh::lean_box(0);
                    if v_isShared_4418_ == 0 {
                        leanh::lean_ctor_set(v___x_4417_, 0, v___x_4554_);
                        v___x_4556_ = v___x_4417_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_4557_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4554_);
                        v___x_4556_ = v_reuseFailAlloc_4557_;
                        state = 47;
                        continue;
                    }
                }
            }
            23 => {
                if leanh::lean_obj_tag(v_a_4428_) == 1 {
                    leanh::lean_del_object(v___x_4430_);
                    v_val_4432_ = leanh::lean_ctor_get(v_a_4428_, 0);
                    v_isSharedCheck_4532_ = (!leanh::lean_is_exclusive(v_a_4428_)) as u8;
                    if v_isSharedCheck_4532_ == 0 {
                        v___x_4434_ = v_a_4428_;
                        v_isShared_4435_ = v_isSharedCheck_4532_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4432_);
                        leanh::lean_dec(v_a_4428_);
                        v___x_4434_ = leanh::lean_box(0);
                        v_isShared_4435_ = v_isSharedCheck_4532_;
                        state = 24;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4428_);
                    leanh::lean_dec_ref_known(v___x_4424_, 2);
                    leanh::lean_dec(v_a_4421_);
                    leanh::lean_dec(v_a_4415_);
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v___x_4533_ = leanh::lean_box(0);
                    if v_isShared_4431_ == 0 {
                        leanh::lean_ctor_set(v___x_4430_, 0, v___x_4533_);
                        v___x_4535_ = v___x_4430_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_4536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
                        v___x_4535_ = v_reuseFailAlloc_4536_;
                        state = 42;
                        continue;
                    }
                }
            }
            24 => {
                v___x_4436_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__23;
                leanh::lean_inc_ref(v___x_4424_);
                v___x_4437_ = l_Lean_mkConst(v___x_4436_, v___x_4424_);
                leanh::lean_inc_ref(v_op_4195_);
                leanh::lean_inc_ref(v_binderType_4383_);
                v___x_4438_ = l_Lean_mkAppB(v___x_4437_, v_binderType_4383_, v_op_4195_);
                v___x_4439_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v___x_4438_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if leanh::lean_obj_tag(v___x_4439_) == 0 {
                    v_a_4440_ = leanh::lean_ctor_get(v___x_4439_, 0);
                    leanh::lean_inc(v_a_4440_);
                    leanh::lean_dec_ref_known(v___x_4439_, 1);
                    v___x_4441_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__25;
                    leanh::lean_inc_ref(v___x_4424_);
                    v___x_4442_ = l_Lean_mkConst(v___x_4441_, v___x_4424_);
                    leanh::lean_inc_ref(v_op_4195_);
                    leanh::lean_inc_ref(v_binderType_4383_);
                    v___x_4443_ = l_Lean_mkAppB(v___x_4442_, v_binderType_4383_, v_op_4195_);
                    v___x_4444_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_4443_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if leanh::lean_obj_tag(v___x_4444_) == 0 {
                        v_a_4445_ = leanh::lean_ctor_get(v___x_4444_, 0);
                        leanh::lean_inc(v_a_4445_);
                        leanh::lean_dec_ref_known(v___x_4444_, 1);
                        leanh::lean_inc_ref(v_binderType_4383_);
                        if v_isShared_4435_ == 0 {
                            leanh::lean_ctor_set(v___x_4434_, 0, v_binderType_4383_);
                            v___x_4447_ = v___x_4434_;
                            state = 25;
                            continue;
                        } else {
                            v_reuseFailAlloc_4515_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_4515_,
                                0,
                                v_binderType_4383_,
                            );
                            v___x_4447_ = v_reuseFailAlloc_4515_;
                            state = 25;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4440_);
                        leanh::lean_del_object(v___x_4434_);
                        leanh::lean_dec(v_val_4432_);
                        leanh::lean_dec_ref_known(v___x_4424_, 2);
                        leanh::lean_dec(v_a_4421_);
                        leanh::lean_dec(v_a_4415_);
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4516_ = leanh::lean_ctor_get(v___x_4444_, 0);
                        v_isSharedCheck_4523_ =
                            (!leanh::lean_is_exclusive(v___x_4444_)) as u8;
                        if v_isSharedCheck_4523_ == 0 {
                            v___x_4518_ = v___x_4444_;
                            v_isShared_4519_ = v_isSharedCheck_4523_;
                            state = 38;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4516_);
                            leanh::lean_dec(v___x_4444_);
                            v___x_4518_ = leanh::lean_box(0);
                            v_isShared_4519_ = v_isSharedCheck_4523_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4434_);
                    leanh::lean_dec(v_val_4432_);
                    leanh::lean_dec_ref_known(v___x_4424_, 2);
                    leanh::lean_dec(v_a_4421_);
                    leanh::lean_dec(v_a_4415_);
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v_a_4524_ = leanh::lean_ctor_get(v___x_4439_, 0);
                    v_isSharedCheck_4531_ = (!leanh::lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4531_ == 0 {
                        v___x_4526_ = v___x_4439_;
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4524_);
                        leanh::lean_dec(v___x_4439_);
                        v___x_4526_ = leanh::lean_box(0);
                        v_isShared_4527_ = v_isSharedCheck_4531_;
                        state = 40;
                        continue;
                    }
                }
            }
            25 => {
                v___x_4448_ = 0;
                v___x_4449_ = leanh::lean_box(0);
                v___x_4450_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_4447_,
                    v___x_4448_,
                    v___x_4449_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if leanh::lean_obj_tag(v___x_4450_) == 0 {
                    v_a_4451_ = leanh::lean_ctor_get(v___x_4450_, 0);
                    leanh::lean_inc_n(v_a_4451_, 2);
                    leanh::lean_dec_ref_known(v___x_4450_, 1);
                    v___x_4452_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___closed__27;
                    v___x_4453_ = l_Lean_mkConst(v___x_4452_, v___x_4424_);
                    leanh::lean_inc_ref(v_op_4195_);
                    leanh::lean_inc_ref(v_binderType_4383_);
                    v___x_4454_ =
                        l_Lean_mkApp3(v___x_4453_, v_binderType_4383_, v_op_4195_, v_a_4451_);
                    v___x_4455_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_4454_,
                        v___y_4372_,
                        v___y_4373_,
                        v___y_4374_,
                        v___y_4375_,
                    );
                    if leanh::lean_obj_tag(v___x_4455_) == 0 {
                        v_a_4456_ = leanh::lean_ctor_get(v___x_4455_, 0);
                        leanh::lean_inc(v_a_4456_);
                        leanh::lean_dec_ref_known(v___x_4455_, 1);
                        if leanh::lean_obj_tag(v_a_4456_) == 1 {
                            v___x_4457_ = l_Lean_instantiateExprMVars___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__1___redArg(v_a_4451_, v___y_4373_);
                            v_a_4458_ = leanh::lean_ctor_get(v___x_4457_, 0);
                            v_isSharedCheck_4496_ =
                                (!leanh::lean_is_exclusive(v___x_4457_)) as u8;
                            if v_isSharedCheck_4496_ == 0 {
                                v___x_4460_ = v___x_4457_;
                                v_isShared_4461_ = v_isSharedCheck_4496_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4458_);
                                leanh::lean_dec(v___x_4457_);
                                v___x_4460_ = leanh::lean_box(0);
                                v_isShared_4461_ = v_isSharedCheck_4496_;
                                state = 26;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4456_);
                            leanh::lean_dec(v_a_4451_);
                            v___x_4497_ = leanh::lean_box(0);
                            v___x_4498_ = (leanh::lean_unbox(v_a_4415_) as u8);
                            leanh::lean_dec(v_a_4415_);
                            leanh::lean_inc(v_a_4440_);
                            leanh::lean_inc(v_a_4445_);
                            v___y_4309_ = v_val_4432_;
                            v___y_4310_ = v___x_4498_;
                            v___y_4311_ = v_binderType_4383_;
                            v___y_4312_ = v_a_4445_;
                            v___y_4313_ = v_a_4440_;
                            v___y_4314_ = v_a_4421_;
                            v___y_4315_ = v_a_4445_;
                            v___y_4316_ = v_a_4440_;
                            v_fst_4317_ = v___x_4497_;
                            v_snd_4318_ = v___x_4497_;
                            v___y_4319_ = v___y_4366_;
                            v___y_4320_ = v___y_4367_;
                            v___y_4321_ = v___y_4368_;
                            v___y_4322_ = v___y_4369_;
                            v___y_4323_ = v___y_4370_;
                            v___y_4324_ = v___y_4371_;
                            v___y_4325_ = v___y_4372_;
                            v___y_4326_ = v___y_4373_;
                            v___y_4327_ = v___y_4374_;
                            v___y_4328_ = v___y_4375_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4451_);
                        leanh::lean_dec(v_a_4445_);
                        leanh::lean_dec(v_a_4440_);
                        leanh::lean_dec(v_val_4432_);
                        leanh::lean_dec(v_a_4421_);
                        leanh::lean_dec(v_a_4415_);
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4499_ = leanh::lean_ctor_get(v___x_4455_, 0);
                        v_isSharedCheck_4506_ =
                            (!leanh::lean_is_exclusive(v___x_4455_)) as u8;
                        if v_isSharedCheck_4506_ == 0 {
                            v___x_4501_ = v___x_4455_;
                            v_isShared_4502_ = v_isSharedCheck_4506_;
                            state = 34;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4499_);
                            leanh::lean_dec(v___x_4455_);
                            v___x_4501_ = leanh::lean_box(0);
                            v_isShared_4502_ = v_isSharedCheck_4506_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4445_);
                    leanh::lean_dec(v_a_4440_);
                    leanh::lean_dec(v_val_4432_);
                    leanh::lean_dec_ref_known(v___x_4424_, 2);
                    leanh::lean_dec(v_a_4421_);
                    leanh::lean_dec(v_a_4415_);
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v_a_4507_ = leanh::lean_ctor_get(v___x_4450_, 0);
                    v_isSharedCheck_4514_ = (!leanh::lean_is_exclusive(v___x_4450_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4509_ = v___x_4450_;
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 36;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4507_);
                        leanh::lean_dec(v___x_4450_);
                        v___x_4509_ = leanh::lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 36;
                        continue;
                    }
                }
            }
            26 => {
                v___x_4462_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                    v_a_4458_,
                    v___y_4367_,
                    v___y_4368_,
                    v___y_4369_,
                    v___y_4370_,
                    v___y_4371_,
                    v___y_4372_,
                    v___y_4373_,
                    v___y_4374_,
                    v___y_4375_,
                );
                if leanh::lean_obj_tag(v___x_4462_) == 0 {
                    v_a_4463_ = leanh::lean_ctor_get(v___x_4462_, 0);
                    leanh::lean_inc(v_a_4463_);
                    leanh::lean_dec_ref_known(v___x_4462_, 1);
                    v___x_4464_ = l_Lean_Meta_Grind_getGeneration___redArg(v_op_4195_, v___y_4366_);
                    if leanh::lean_obj_tag(v___x_4464_) == 0 {
                        v_a_4465_ = leanh::lean_ctor_get(v___x_4464_, 0);
                        leanh::lean_inc(v_a_4465_);
                        leanh::lean_dec_ref_known(v___x_4464_, 1);
                        v___x_4466_ = leanh::lean_box(0);
                        leanh::lean_inc(v___y_4375_);
                        leanh::lean_inc_ref(v___y_4374_);
                        leanh::lean_inc(v___y_4373_);
                        leanh::lean_inc_ref(v___y_4372_);
                        leanh::lean_inc(v___y_4371_);
                        leanh::lean_inc_ref(v___y_4370_);
                        leanh::lean_inc(v___y_4369_);
                        leanh::lean_inc_ref(v___y_4368_);
                        leanh::lean_inc(v___y_4367_);
                        leanh::lean_inc(v___y_4366_);
                        leanh::lean_inc(v_a_4463_);
                        v___x_4467_ = lean_grind_internalize(
                            v_a_4463_,
                            v_a_4465_,
                            v___x_4466_,
                            v___y_4366_,
                            v___y_4367_,
                            v___y_4368_,
                            v___y_4369_,
                            v___y_4370_,
                            v___y_4371_,
                            v___y_4372_,
                            v___y_4373_,
                            v___y_4374_,
                            v___y_4375_,
                        );
                        if leanh::lean_obj_tag(v___x_4467_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4467_, 1);
                            if v_isShared_4461_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_4460_, 1);
                                leanh::lean_ctor_set(v___x_4460_, 0, v_a_4463_);
                                v___x_4469_ = v___x_4460_;
                                state = 27;
                                continue;
                            } else {
                                v_reuseFailAlloc_4471_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4463_);
                                v___x_4469_ = v_reuseFailAlloc_4471_;
                                state = 27;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4463_);
                            leanh::lean_del_object(v___x_4460_);
                            leanh::lean_dec_ref_known(v_a_4456_, 1);
                            leanh::lean_dec(v_a_4445_);
                            leanh::lean_dec(v_a_4440_);
                            leanh::lean_dec(v_val_4432_);
                            leanh::lean_dec(v_a_4421_);
                            leanh::lean_dec(v_a_4415_);
                            leanh::lean_dec_ref(v_binderType_4383_);
                            leanh::lean_dec_ref(v_op_4195_);
                            v_a_4472_ = leanh::lean_ctor_get(v___x_4467_, 0);
                            v_isSharedCheck_4479_ =
                                (!leanh::lean_is_exclusive(v___x_4467_)) as u8;
                            if v_isSharedCheck_4479_ == 0 {
                                v___x_4474_ = v___x_4467_;
                                v_isShared_4475_ = v_isSharedCheck_4479_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4472_);
                                leanh::lean_dec(v___x_4467_);
                                v___x_4474_ = leanh::lean_box(0);
                                v_isShared_4475_ = v_isSharedCheck_4479_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_4463_);
                        leanh::lean_del_object(v___x_4460_);
                        leanh::lean_dec_ref_known(v_a_4456_, 1);
                        leanh::lean_dec(v_a_4445_);
                        leanh::lean_dec(v_a_4440_);
                        leanh::lean_dec(v_val_4432_);
                        leanh::lean_dec(v_a_4421_);
                        leanh::lean_dec(v_a_4415_);
                        leanh::lean_dec_ref(v_binderType_4383_);
                        leanh::lean_dec_ref(v_op_4195_);
                        v_a_4480_ = leanh::lean_ctor_get(v___x_4464_, 0);
                        v_isSharedCheck_4487_ =
                            (!leanh::lean_is_exclusive(v___x_4464_)) as u8;
                        if v_isSharedCheck_4487_ == 0 {
                            v___x_4482_ = v___x_4464_;
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4480_);
                            leanh::lean_dec(v___x_4464_);
                            v___x_4482_ = leanh::lean_box(0);
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4460_);
                    leanh::lean_dec_ref_known(v_a_4456_, 1);
                    leanh::lean_dec(v_a_4445_);
                    leanh::lean_dec(v_a_4440_);
                    leanh::lean_dec(v_val_4432_);
                    leanh::lean_dec(v_a_4421_);
                    leanh::lean_dec(v_a_4415_);
                    leanh::lean_dec_ref(v_binderType_4383_);
                    leanh::lean_dec_ref(v_op_4195_);
                    v_a_4488_ = leanh::lean_ctor_get(v___x_4462_, 0);
                    v_isSharedCheck_4495_ = (!leanh::lean_is_exclusive(v___x_4462_)) as u8;
                    if v_isSharedCheck_4495_ == 0 {
                        v___x_4490_ = v___x_4462_;
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4488_);
                        leanh::lean_dec(v___x_4462_);
                        v___x_4490_ = leanh::lean_box(0);
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 32;
                        continue;
                    }
                }
            }
            27 => {
                v___x_4470_ = (leanh::lean_unbox(v_a_4415_) as u8);
                leanh::lean_dec(v_a_4415_);
                leanh::lean_inc(v_a_4440_);
                leanh::lean_inc(v_a_4445_);
                v___y_4309_ = v_val_4432_;
                v___y_4310_ = v___x_4470_;
                v___y_4311_ = v_binderType_4383_;
                v___y_4312_ = v_a_4445_;
                v___y_4313_ = v_a_4440_;
                v___y_4314_ = v_a_4421_;
                v___y_4315_ = v_a_4445_;
                v___y_4316_ = v_a_4440_;
                v_fst_4317_ = v_a_4456_;
                v_snd_4318_ = v___x_4469_;
                v___y_4319_ = v___y_4366_;
                v___y_4320_ = v___y_4367_;
                v___y_4321_ = v___y_4368_;
                v___y_4322_ = v___y_4369_;
                v___y_4323_ = v___y_4370_;
                v___y_4324_ = v___y_4371_;
                v___y_4325_ = v___y_4372_;
                v___y_4326_ = v___y_4373_;
                v___y_4327_ = v___y_4374_;
                v___y_4328_ = v___y_4375_;
                state = 10;
                continue;
            }
            28 => {
                if v_isShared_4475_ == 0 {
                    v___x_4477_ = v___x_4474_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4478_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
                    v___x_4477_ = v_reuseFailAlloc_4478_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4477_;
            }
            30 => {
                if v_isShared_4483_ == 0 {
                    v___x_4485_ = v___x_4482_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
                    v___x_4485_ = v_reuseFailAlloc_4486_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4485_;
            }
            32 => {
                if v_isShared_4491_ == 0 {
                    v___x_4493_ = v___x_4490_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4494_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
                    v___x_4493_ = v_reuseFailAlloc_4494_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4493_;
            }
            34 => {
                if v_isShared_4502_ == 0 {
                    v___x_4504_ = v___x_4501_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4505_, 0, v_a_4499_);
                    v___x_4504_ = v_reuseFailAlloc_4505_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4504_;
            }
            36 => {
                if v_isShared_4510_ == 0 {
                    v___x_4512_ = v___x_4509_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4512_;
            }
            38 => {
                if v_isShared_4519_ == 0 {
                    v___x_4521_ = v___x_4518_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4522_, 0, v_a_4516_);
                    v___x_4521_ = v_reuseFailAlloc_4522_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4521_;
            }
            40 => {
                if v_isShared_4527_ == 0 {
                    v___x_4529_ = v___x_4526_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4530_, 0, v_a_4524_);
                    v___x_4529_ = v_reuseFailAlloc_4530_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4529_;
            }
            42 => {
                return v___x_4535_;
            }
            43 => {
                if v_isShared_4541_ == 0 {
                    v___x_4543_ = v___x_4540_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4543_;
            }
            45 => {
                if v_isShared_4549_ == 0 {
                    v___x_4551_ = v___x_4548_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4552_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
                    v___x_4551_ = v_reuseFailAlloc_4552_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4551_;
            }
            47 => {
                return v___x_4556_;
            }
            48 => {
                if v_isShared_4562_ == 0 {
                    v___x_4564_ = v___x_4561_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
                    v___x_4564_ = v_reuseFailAlloc_4565_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4564_;
            }
            50 => {
                if v_isShared_4571_ == 0 {
                    v___x_4573_ = v___x_4570_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
                    v___x_4573_ = v_reuseFailAlloc_4574_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_4573_;
            }
            52 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_4582_;
            }
            54 => {
                return v___x_4587_;
            }
            55 => {
                return v___x_4591_;
            }
            56 => {
                if v_isShared_4597_ == 0 {
                    v___x_4599_ = v___x_4596_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_4600_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_a_4594_);
                    v___x_4599_ = v_reuseFailAlloc_4600_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_4599_;
            }
            58 => {
                return v___x_4604_;
            }
            59 => {
                return v___x_4608_;
            }
            60 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_4616_;
            }
            62 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go___boxed(
    mut v_op_4632_: *mut leanh::LeanObject,
    mut v_a_4633_: *mut leanh::LeanObject,
    mut v_a_4634_: *mut leanh::LeanObject,
    mut v_a_4635_: *mut leanh::LeanObject,
    mut v_a_4636_: *mut leanh::LeanObject,
    mut v_a_4637_: *mut leanh::LeanObject,
    mut v_a_4638_: *mut leanh::LeanObject,
    mut v_a_4639_: *mut leanh::LeanObject,
    mut v_a_4640_: *mut leanh::LeanObject,
    mut v_a_4641_: *mut leanh::LeanObject,
    mut v_a_4642_: *mut leanh::LeanObject,
    mut v_a_4643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4644_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(
        v_op_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_, v_a_4639_,
        v_a_4640_, v_a_4641_, v_a_4642_,
    );
    leanh::lean_dec(v_a_4642_);
    leanh::lean_dec_ref(v_a_4641_);
    leanh::lean_dec(v_a_4640_);
    leanh::lean_dec_ref(v_a_4639_);
    leanh::lean_dec(v_a_4638_);
    leanh::lean_dec_ref(v_a_4637_);
    leanh::lean_dec(v_a_4636_);
    leanh::lean_dec_ref(v_a_4635_);
    leanh::lean_dec(v_a_4634_);
    leanh::lean_dec(v_a_4633_);
    return v_res_4644_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(
    mut v_cls_4645_: *mut leanh::LeanObject,
    mut v_msg_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
    mut v___y_4652_: *mut leanh::LeanObject,
    mut v___y_4653_: *mut leanh::LeanObject,
    mut v___y_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4658_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___redArg(v_cls_4645_, v_msg_4646_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
    return v___x_4658_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0___boxed(
    mut v_cls_4659_: *mut leanh::LeanObject,
    mut v_msg_4660_: *mut leanh::LeanObject,
    mut v___y_4661_: *mut leanh::LeanObject,
    mut v___y_4662_: *mut leanh::LeanObject,
    mut v___y_4663_: *mut leanh::LeanObject,
    mut v___y_4664_: *mut leanh::LeanObject,
    mut v___y_4665_: *mut leanh::LeanObject,
    mut v___y_4666_: *mut leanh::LeanObject,
    mut v___y_4667_: *mut leanh::LeanObject,
    mut v___y_4668_: *mut leanh::LeanObject,
    mut v___y_4669_: *mut leanh::LeanObject,
    mut v___y_4670_: *mut leanh::LeanObject,
    mut v___y_4671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4672_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__0(v_cls_4659_, v_msg_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
    leanh::lean_dec(v___y_4670_);
    leanh::lean_dec_ref(v___y_4669_);
    leanh::lean_dec(v___y_4668_);
    leanh::lean_dec_ref(v___y_4667_);
    leanh::lean_dec(v___y_4666_);
    leanh::lean_dec_ref(v___y_4665_);
    leanh::lean_dec(v___y_4664_);
    leanh::lean_dec_ref(v___y_4663_);
    leanh::lean_dec(v___y_4662_);
    leanh::lean_dec(v___y_4661_);
    return v_res_4672_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(
    mut v_00_u03b2_4673_: *mut leanh::LeanObject,
    mut v_m_4674_: *mut leanh::LeanObject,
    mut v_a_4675_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4676_: u8 = 0;
    v___x_4676_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___redArg(v_m_4674_, v_a_4675_);
    return v___x_4676_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2___boxed(
    mut v_00_u03b2_4677_: *mut leanh::LeanObject,
    mut v_m_4678_: *mut leanh::LeanObject,
    mut v_a_4679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4680_: u8 = 0;
    let mut v_r_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4680_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go_spec__2(v_00_u03b2_4677_, v_m_4678_, v_a_4679_);
    leanh::lean_dec(v_a_4679_);
    leanh::lean_dec_ref(v_m_4678_);
    v_r_4681_ = leanh::lean_box((v_res_4680_) as usize);
    return v_r_4681_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0(
    mut v_op_4682_: *mut leanh::LeanObject,
    mut v_a_4683_: *mut leanh::LeanObject,
    mut v_s_4684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_structs_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opIdOf_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToOpIds_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4691_: u8 = 0;
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_4685_ = leanh::lean_ctor_get(v_s_4684_, 0);
                v_opIdOf_4686_ = leanh::lean_ctor_get(v_s_4684_, 1);
                v_exprToOpIds_4687_ = leanh::lean_ctor_get(v_s_4684_, 2);
                v_steps_4688_ = leanh::lean_ctor_get(v_s_4684_, 3);
                v_isSharedCheck_4696_ = (!leanh::lean_is_exclusive(v_s_4684_)) as u8;
                if v_isSharedCheck_4696_ == 0 {
                    v___x_4690_ = v_s_4684_;
                    v_isShared_4691_ = v_isSharedCheck_4696_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_steps_4688_);
                    leanh::lean_inc(v_exprToOpIds_4687_);
                    leanh::lean_inc(v_opIdOf_4686_);
                    leanh::lean_inc(v_structs_4685_);
                    leanh::lean_dec(v_s_4684_);
                    v___x_4690_ = leanh::lean_box(0);
                    v_isShared_4691_ = v_isSharedCheck_4696_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4692_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_insertOpId_spec__0___redArg(v_opIdOf_4686_, v_op_4682_, v_a_4683_);
                if v_isShared_4691_ == 0 {
                    leanh::lean_ctor_set(v___x_4690_, 1, v___x_4692_);
                    v___x_4694_ = v___x_4690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4695_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4695_, 0, v_structs_4685_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4695_, 1, v___x_4692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4695_, 2, v_exprToOpIds_4687_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4695_, 3, v_steps_4688_);
                    v___x_4694_ = v_reuseFailAlloc_4695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId_x3f(
    mut v_op_4697_: *mut leanh::LeanObject,
    mut v_a_4698_: *mut leanh::LeanObject,
    mut v_a_4699_: *mut leanh::LeanObject,
    mut v_a_4700_: *mut leanh::LeanObject,
    mut v_a_4701_: *mut leanh::LeanObject,
    mut v_a_4702_: *mut leanh::LeanObject,
    mut v_a_4703_: *mut leanh::LeanObject,
    mut v_a_4704_: *mut leanh::LeanObject,
    mut v_a_4705_: *mut leanh::LeanObject,
    mut v_a_4706_: *mut leanh::LeanObject,
    mut v_a_4707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4713_: u8 = 0;
    let mut v_opIdOf_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4731_: u8 = 0;
    let mut v_unused_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_a_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4745_: u8 = 0;
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4709_ = l_Lean_Meta_Grind_AC_get_x27___redArg(v_a_4698_, v_a_4706_);
                if leanh::lean_obj_tag(v___x_4709_) == 0 {
                    v_a_4710_ = leanh::lean_ctor_get(v___x_4709_, 0);
                    v_isSharedCheck_4741_ = (!leanh::lean_is_exclusive(v___x_4709_)) as u8;
                    if v_isSharedCheck_4741_ == 0 {
                        v___x_4712_ = v___x_4709_;
                        v_isShared_4713_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4710_);
                        leanh::lean_dec(v___x_4709_);
                        v___x_4712_ = leanh::lean_box(0);
                        v_isShared_4713_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_op_4697_);
                    v_a_4742_ = leanh::lean_ctor_get(v___x_4709_, 0);
                    v_isSharedCheck_4749_ = (!leanh::lean_is_exclusive(v___x_4709_)) as u8;
                    if v_isSharedCheck_4749_ == 0 {
                        v___x_4744_ = v___x_4709_;
                        v_isShared_4745_ = v_isSharedCheck_4749_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4742_);
                        leanh::lean_dec(v___x_4709_);
                        v___x_4744_ = leanh::lean_box(0);
                        v_isShared_4745_ = v_isSharedCheck_4749_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_opIdOf_4714_ = leanh::lean_ctor_get(v_a_4710_, 1);
                leanh::lean_inc_ref(v_opIdOf_4714_);
                leanh::lean_dec(v_a_4710_);
                v___x_4715_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_AC_getTermOpIds_spec__0___redArg(v_opIdOf_4714_, v_op_4697_);
                leanh::lean_dec_ref(v_opIdOf_4714_);
                if leanh::lean_obj_tag(v___x_4715_) == 1 {
                    leanh::lean_dec_ref(v_op_4697_);
                    v_val_4716_ = leanh::lean_ctor_get(v___x_4715_, 0);
                    leanh::lean_inc(v_val_4716_);
                    leanh::lean_dec_ref_known(v___x_4715_, 1);
                    if v_isShared_4713_ == 0 {
                        leanh::lean_ctor_set(v___x_4712_, 0, v_val_4716_);
                        v___x_4718_ = v___x_4712_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4719_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_val_4716_);
                        v___x_4718_ = v_reuseFailAlloc_4719_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4715_);
                    leanh::lean_del_object(v___x_4712_);
                    leanh::lean_inc_ref(v_op_4697_);
                    v___x_4720_ = l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_getOpId_x3f_go(v_op_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_, v_a_4707_);
                    if leanh::lean_obj_tag(v___x_4720_) == 0 {
                        v_a_4721_ = leanh::lean_ctor_get(v___x_4720_, 0);
                        leanh::lean_inc_n(v_a_4721_, 2);
                        leanh::lean_dec_ref_known(v___x_4720_, 1);
                        v___f_4722_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_AC_getOpId_x3f___lam__0 as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_4722_, 0, v_op_4697_);
                        leanh::lean_closure_set(v___f_4722_, 1, v_a_4721_);
                        v___x_4723_ = l_Lean_Meta_Grind_AC_acExt;
                        v___x_4724_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_4723_, v___f_4722_, v_a_4698_);
                        if leanh::lean_obj_tag(v___x_4724_) == 0 {
                            v_isSharedCheck_4731_ =
                                (!leanh::lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4731_ == 0 {
                                v_unused_4732_ = leanh::lean_ctor_get(v___x_4724_, 0);
                                leanh::lean_dec(v_unused_4732_);
                                v___x_4726_ = v___x_4724_;
                                v_isShared_4727_ = v_isSharedCheck_4731_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_4724_);
                                v___x_4726_ = leanh::lean_box(0);
                                v_isShared_4727_ = v_isSharedCheck_4731_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4721_);
                            v_a_4733_ = leanh::lean_ctor_get(v___x_4724_, 0);
                            v_isSharedCheck_4740_ =
                                (!leanh::lean_is_exclusive(v___x_4724_)) as u8;
                            if v_isSharedCheck_4740_ == 0 {
                                v___x_4735_ = v___x_4724_;
                                v_isShared_4736_ = v_isSharedCheck_4740_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4733_);
                                leanh::lean_dec(v___x_4724_);
                                v___x_4735_ = leanh::lean_box(0);
                                v_isShared_4736_ = v_isSharedCheck_4740_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_op_4697_);
                        return v___x_4720_;
                    }
                }
            }
            2 => {
                return v___x_4718_;
            }
            3 => {
                if v_isShared_4727_ == 0 {
                    leanh::lean_ctor_set(v___x_4726_, 0, v_a_4721_);
                    v___x_4729_ = v___x_4726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4730_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4721_);
                    v___x_4729_ = v_reuseFailAlloc_4730_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4729_;
            }
            5 => {
                if v_isShared_4736_ == 0 {
                    v___x_4738_ = v___x_4735_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
                    v___x_4738_ = v_reuseFailAlloc_4739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4738_;
            }
            7 => {
                if v_isShared_4745_ == 0 {
                    v___x_4747_ = v___x_4744_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4748_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
                    v___x_4747_ = v_reuseFailAlloc_4748_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_getOpId_x3f___boxed(
    mut v_op_4750_: *mut leanh::LeanObject,
    mut v_a_4751_: *mut leanh::LeanObject,
    mut v_a_4752_: *mut leanh::LeanObject,
    mut v_a_4753_: *mut leanh::LeanObject,
    mut v_a_4754_: *mut leanh::LeanObject,
    mut v_a_4755_: *mut leanh::LeanObject,
    mut v_a_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
    mut v_a_4758_: *mut leanh::LeanObject,
    mut v_a_4759_: *mut leanh::LeanObject,
    mut v_a_4760_: *mut leanh::LeanObject,
    mut v_a_4761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4762_ = l_Lean_Meta_Grind_AC_getOpId_x3f(
        v_op_4750_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_,
        v_a_4758_, v_a_4759_, v_a_4760_,
    );
    leanh::lean_dec(v_a_4760_);
    leanh::lean_dec_ref(v_a_4759_);
    leanh::lean_dec(v_a_4758_);
    leanh::lean_dec_ref(v_a_4757_);
    leanh::lean_dec(v_a_4756_);
    leanh::lean_dec_ref(v_a_4755_);
    leanh::lean_dec(v_a_4754_);
    leanh::lean_dec_ref(v_a_4753_);
    leanh::lean_dec(v_a_4752_);
    leanh::lean_dec(v_a_4751_);
    return v_res_4762_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_isOp_x3f(
    mut v_e_4763_: *mut leanh::LeanObject,
    mut v_a_4764_: *mut leanh::LeanObject,
    mut v_a_4765_: *mut leanh::LeanObject,
    mut v_a_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
    mut v_a_4768_: *mut leanh::LeanObject,
    mut v_a_4769_: *mut leanh::LeanObject,
    mut v_a_4770_: *mut leanh::LeanObject,
    mut v_a_4771_: *mut leanh::LeanObject,
    mut v_a_4772_: *mut leanh::LeanObject,
    mut v_a_4773_: *mut leanh::LeanObject,
    mut v_a_4774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4777_: u8 = 0;
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4784_: u8 = 0;
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: u8 = 0;
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4799_: u8 = 0;
    let mut v_a_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4803_: u8 = 0;
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v___x_4808_: u8 = 0;
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4808_ = l_Lean_Expr_isApp(v_e_4763_);
                if v___x_4808_ == 0 {
                    v___y_4777_ = v___x_4808_;
                    state = 1;
                    continue;
                } else {
                    v___x_4809_ = l_Lean_Expr_appFn_x21(v_e_4763_);
                    v___x_4810_ = l_Lean_Expr_isApp(v___x_4809_);
                    leanh::lean_dec_ref(v___x_4809_);
                    v___y_4777_ = v___x_4810_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4777_ == 0 {
                    v___x_4778_ = leanh::lean_box(0);
                    v___x_4779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4779_, 0, v___x_4778_);
                    return v___x_4779_;
                } else {
                    v___x_4780_ = l_Lean_Meta_Grind_AC_getOp(
                        v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_,
                        v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_,
                    );
                    if leanh::lean_obj_tag(v___x_4780_) == 0 {
                        v_a_4781_ = leanh::lean_ctor_get(v___x_4780_, 0);
                        v_isSharedCheck_4799_ =
                            (!leanh::lean_is_exclusive(v___x_4780_)) as u8;
                        if v_isSharedCheck_4799_ == 0 {
                            v___x_4783_ = v___x_4780_;
                            v_isShared_4784_ = v_isSharedCheck_4799_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4781_);
                            leanh::lean_dec(v___x_4780_);
                            v___x_4783_ = leanh::lean_box(0);
                            v_isShared_4784_ = v_isSharedCheck_4799_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_4800_ = leanh::lean_ctor_get(v___x_4780_, 0);
                        v_isSharedCheck_4807_ =
                            (!leanh::lean_is_exclusive(v___x_4780_)) as u8;
                        if v_isSharedCheck_4807_ == 0 {
                            v___x_4802_ = v___x_4780_;
                            v_isShared_4803_ = v_isSharedCheck_4807_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4800_);
                            leanh::lean_dec(v___x_4780_);
                            v___x_4802_ = leanh::lean_box(0);
                            v_isShared_4803_ = v_isSharedCheck_4807_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4785_ = l_Lean_Expr_appFn_x21(v_e_4763_);
                v___x_4786_ = l_Lean_Expr_appFn_x21(v___x_4785_);
                v___x_4787_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_4786_,
                        v_a_4781_,
                    );
                leanh::lean_dec(v_a_4781_);
                leanh::lean_dec_ref(v___x_4786_);
                if v___x_4787_ == 0 {
                    leanh::lean_dec_ref(v___x_4785_);
                    v___x_4788_ = leanh::lean_box(0);
                    if v_isShared_4784_ == 0 {
                        leanh::lean_ctor_set(v___x_4783_, 0, v___x_4788_);
                        v___x_4790_ = v___x_4783_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4791_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4788_);
                        v___x_4790_ = v_reuseFailAlloc_4791_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4792_ = l_Lean_Expr_appArg_x21(v___x_4785_);
                    leanh::lean_dec_ref(v___x_4785_);
                    v___x_4793_ = l_Lean_Expr_appArg_x21(v_e_4763_);
                    v___x_4794_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4794_, 0, v___x_4792_);
                    leanh::lean_ctor_set(v___x_4794_, 1, v___x_4793_);
                    v___x_4795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4795_, 0, v___x_4794_);
                    if v_isShared_4784_ == 0 {
                        leanh::lean_ctor_set(v___x_4783_, 0, v___x_4795_);
                        v___x_4797_ = v___x_4783_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4798_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4795_);
                        v___x_4797_ = v_reuseFailAlloc_4798_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4790_;
            }
            4 => {
                return v___x_4797_;
            }
            5 => {
                if v_isShared_4803_ == 0 {
                    v___x_4805_ = v___x_4802_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
                    v___x_4805_ = v_reuseFailAlloc_4806_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_isOp_x3f___boxed(
    mut v_e_4811_: *mut leanh::LeanObject,
    mut v_a_4812_: *mut leanh::LeanObject,
    mut v_a_4813_: *mut leanh::LeanObject,
    mut v_a_4814_: *mut leanh::LeanObject,
    mut v_a_4815_: *mut leanh::LeanObject,
    mut v_a_4816_: *mut leanh::LeanObject,
    mut v_a_4817_: *mut leanh::LeanObject,
    mut v_a_4818_: *mut leanh::LeanObject,
    mut v_a_4819_: *mut leanh::LeanObject,
    mut v_a_4820_: *mut leanh::LeanObject,
    mut v_a_4821_: *mut leanh::LeanObject,
    mut v_a_4822_: *mut leanh::LeanObject,
    mut v_a_4823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4824_ = l_Lean_Meta_Grind_AC_isOp_x3f(
        v_e_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_, v_a_4817_, v_a_4818_,
        v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_,
    );
    leanh::lean_dec(v_a_4822_);
    leanh::lean_dec_ref(v_a_4821_);
    leanh::lean_dec(v_a_4820_);
    leanh::lean_dec_ref(v_a_4819_);
    leanh::lean_dec(v_a_4818_);
    leanh::lean_dec_ref(v_a_4817_);
    leanh::lean_dec(v_a_4816_);
    leanh::lean_dec_ref(v_a_4815_);
    leanh::lean_dec(v_a_4814_);
    leanh::lean_dec(v_a_4813_);
    leanh::lean_dec(v_a_4812_);
    leanh::lean_dec_ref(v_e_4811_);
    return v_res_4824_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_isCommutative(
    mut v_a_4825_: *mut leanh::LeanObject,
    mut v_a_4826_: *mut leanh::LeanObject,
    mut v_a_4827_: *mut leanh::LeanObject,
    mut v_a_4828_: *mut leanh::LeanObject,
    mut v_a_4829_: *mut leanh::LeanObject,
    mut v_a_4830_: *mut leanh::LeanObject,
    mut v_a_4831_: *mut leanh::LeanObject,
    mut v_a_4832_: *mut leanh::LeanObject,
    mut v_a_4833_: *mut leanh::LeanObject,
    mut v_a_4834_: *mut leanh::LeanObject,
    mut v_a_4835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4841_: u8 = 0;
    let mut v_commInst_x3f_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: u8 = 0;
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: u8 = 0;
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4853_: u8 = 0;
    let mut v_a_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4857_: u8 = 0;
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4837_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_, v_a_4830_, v_a_4831_,
                    v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_,
                );
                if leanh::lean_obj_tag(v___x_4837_) == 0 {
                    v_a_4838_ = leanh::lean_ctor_get(v___x_4837_, 0);
                    v_isSharedCheck_4853_ = (!leanh::lean_is_exclusive(v___x_4837_)) as u8;
                    if v_isSharedCheck_4853_ == 0 {
                        v___x_4840_ = v___x_4837_;
                        v_isShared_4841_ = v_isSharedCheck_4853_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4838_);
                        leanh::lean_dec(v___x_4837_);
                        v___x_4840_ = leanh::lean_box(0);
                        v_isShared_4841_ = v_isSharedCheck_4853_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4854_ = leanh::lean_ctor_get(v___x_4837_, 0);
                    v_isSharedCheck_4861_ = (!leanh::lean_is_exclusive(v___x_4837_)) as u8;
                    if v_isSharedCheck_4861_ == 0 {
                        v___x_4856_ = v___x_4837_;
                        v_isShared_4857_ = v_isSharedCheck_4861_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4854_);
                        leanh::lean_dec(v___x_4837_);
                        v___x_4856_ = leanh::lean_box(0);
                        v_isShared_4857_ = v_isSharedCheck_4861_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_commInst_x3f_4842_ = leanh::lean_ctor_get(v_a_4838_, 7);
                leanh::lean_inc(v_commInst_x3f_4842_);
                leanh::lean_dec(v_a_4838_);
                if leanh::lean_obj_tag(v_commInst_x3f_4842_) == 0 {
                    v___x_4843_ = 0;
                    v___x_4844_ = leanh::lean_box((v___x_4843_) as usize);
                    if v_isShared_4841_ == 0 {
                        leanh::lean_ctor_set(v___x_4840_, 0, v___x_4844_);
                        v___x_4846_ = v___x_4840_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
                        v___x_4846_ = v_reuseFailAlloc_4847_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_commInst_x3f_4842_, 1);
                    v___x_4848_ = 1;
                    v___x_4849_ = leanh::lean_box((v___x_4848_) as usize);
                    if v_isShared_4841_ == 0 {
                        leanh::lean_ctor_set(v___x_4840_, 0, v___x_4849_);
                        v___x_4851_ = v___x_4840_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4852_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
                        v___x_4851_ = v_reuseFailAlloc_4852_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4846_;
            }
            3 => {
                return v___x_4851_;
            }
            4 => {
                if v_isShared_4857_ == 0 {
                    v___x_4859_ = v___x_4856_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4860_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
                    v___x_4859_ = v_reuseFailAlloc_4860_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_isCommutative___boxed(
    mut v_a_4862_: *mut leanh::LeanObject,
    mut v_a_4863_: *mut leanh::LeanObject,
    mut v_a_4864_: *mut leanh::LeanObject,
    mut v_a_4865_: *mut leanh::LeanObject,
    mut v_a_4866_: *mut leanh::LeanObject,
    mut v_a_4867_: *mut leanh::LeanObject,
    mut v_a_4868_: *mut leanh::LeanObject,
    mut v_a_4869_: *mut leanh::LeanObject,
    mut v_a_4870_: *mut leanh::LeanObject,
    mut v_a_4871_: *mut leanh::LeanObject,
    mut v_a_4872_: *mut leanh::LeanObject,
    mut v_a_4873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4874_ = l_Lean_Meta_Grind_AC_isCommutative(
        v_a_4862_, v_a_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_,
        v_a_4870_, v_a_4871_, v_a_4872_,
    );
    leanh::lean_dec(v_a_4872_);
    leanh::lean_dec_ref(v_a_4871_);
    leanh::lean_dec(v_a_4870_);
    leanh::lean_dec_ref(v_a_4869_);
    leanh::lean_dec(v_a_4868_);
    leanh::lean_dec_ref(v_a_4867_);
    leanh::lean_dec(v_a_4866_);
    leanh::lean_dec_ref(v_a_4865_);
    leanh::lean_dec(v_a_4864_);
    leanh::lean_dec(v_a_4863_);
    leanh::lean_dec(v_a_4862_);
    return v_res_4874_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_hasNeutral(
    mut v_a_4875_: *mut leanh::LeanObject,
    mut v_a_4876_: *mut leanh::LeanObject,
    mut v_a_4877_: *mut leanh::LeanObject,
    mut v_a_4878_: *mut leanh::LeanObject,
    mut v_a_4879_: *mut leanh::LeanObject,
    mut v_a_4880_: *mut leanh::LeanObject,
    mut v_a_4881_: *mut leanh::LeanObject,
    mut v_a_4882_: *mut leanh::LeanObject,
    mut v_a_4883_: *mut leanh::LeanObject,
    mut v_a_4884_: *mut leanh::LeanObject,
    mut v_a_4885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4891_: u8 = 0;
    let mut v_neutralInst_x3f_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: u8 = 0;
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: u8 = 0;
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4903_: u8 = 0;
    let mut v_a_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4907_: u8 = 0;
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4887_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_,
                    v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_,
                );
                if leanh::lean_obj_tag(v___x_4887_) == 0 {
                    v_a_4888_ = leanh::lean_ctor_get(v___x_4887_, 0);
                    v_isSharedCheck_4903_ = (!leanh::lean_is_exclusive(v___x_4887_)) as u8;
                    if v_isSharedCheck_4903_ == 0 {
                        v___x_4890_ = v___x_4887_;
                        v_isShared_4891_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4888_);
                        leanh::lean_dec(v___x_4887_);
                        v___x_4890_ = leanh::lean_box(0);
                        v_isShared_4891_ = v_isSharedCheck_4903_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4904_ = leanh::lean_ctor_get(v___x_4887_, 0);
                    v_isSharedCheck_4911_ = (!leanh::lean_is_exclusive(v___x_4887_)) as u8;
                    if v_isSharedCheck_4911_ == 0 {
                        v___x_4906_ = v___x_4887_;
                        v_isShared_4907_ = v_isSharedCheck_4911_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4904_);
                        leanh::lean_dec(v___x_4887_);
                        v___x_4906_ = leanh::lean_box(0);
                        v_isShared_4907_ = v_isSharedCheck_4911_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_neutralInst_x3f_4892_ = leanh::lean_ctor_get(v_a_4888_, 8);
                leanh::lean_inc(v_neutralInst_x3f_4892_);
                leanh::lean_dec(v_a_4888_);
                if leanh::lean_obj_tag(v_neutralInst_x3f_4892_) == 0 {
                    v___x_4893_ = 0;
                    v___x_4894_ = leanh::lean_box((v___x_4893_) as usize);
                    if v_isShared_4891_ == 0 {
                        leanh::lean_ctor_set(v___x_4890_, 0, v___x_4894_);
                        v___x_4896_ = v___x_4890_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4897_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4897_, 0, v___x_4894_);
                        v___x_4896_ = v_reuseFailAlloc_4897_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_neutralInst_x3f_4892_, 1);
                    v___x_4898_ = 1;
                    v___x_4899_ = leanh::lean_box((v___x_4898_) as usize);
                    if v_isShared_4891_ == 0 {
                        leanh::lean_ctor_set(v___x_4890_, 0, v___x_4899_);
                        v___x_4901_ = v___x_4890_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
                        v___x_4901_ = v_reuseFailAlloc_4902_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4896_;
            }
            3 => {
                return v___x_4901_;
            }
            4 => {
                if v_isShared_4907_ == 0 {
                    v___x_4909_ = v___x_4906_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_a_4904_);
                    v___x_4909_ = v_reuseFailAlloc_4910_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_hasNeutral___boxed(
    mut v_a_4912_: *mut leanh::LeanObject,
    mut v_a_4913_: *mut leanh::LeanObject,
    mut v_a_4914_: *mut leanh::LeanObject,
    mut v_a_4915_: *mut leanh::LeanObject,
    mut v_a_4916_: *mut leanh::LeanObject,
    mut v_a_4917_: *mut leanh::LeanObject,
    mut v_a_4918_: *mut leanh::LeanObject,
    mut v_a_4919_: *mut leanh::LeanObject,
    mut v_a_4920_: *mut leanh::LeanObject,
    mut v_a_4921_: *mut leanh::LeanObject,
    mut v_a_4922_: *mut leanh::LeanObject,
    mut v_a_4923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_Meta_Grind_AC_hasNeutral(
        v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_,
        v_a_4920_, v_a_4921_, v_a_4922_,
    );
    leanh::lean_dec(v_a_4922_);
    leanh::lean_dec_ref(v_a_4921_);
    leanh::lean_dec(v_a_4920_);
    leanh::lean_dec_ref(v_a_4919_);
    leanh::lean_dec(v_a_4918_);
    leanh::lean_dec_ref(v_a_4917_);
    leanh::lean_dec(v_a_4916_);
    leanh::lean_dec_ref(v_a_4915_);
    leanh::lean_dec(v_a_4914_);
    leanh::lean_dec(v_a_4913_);
    leanh::lean_dec(v_a_4912_);
    return v_res_4924_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_isIdempotent(
    mut v_a_4925_: *mut leanh::LeanObject,
    mut v_a_4926_: *mut leanh::LeanObject,
    mut v_a_4927_: *mut leanh::LeanObject,
    mut v_a_4928_: *mut leanh::LeanObject,
    mut v_a_4929_: *mut leanh::LeanObject,
    mut v_a_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
    mut v_a_4934_: *mut leanh::LeanObject,
    mut v_a_4935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v_idempotentInst_x3f_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: u8 = 0;
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4953_: u8 = 0;
    let mut v_a_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4957_: u8 = 0;
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4937_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                    v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_,
                    v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_,
                );
                if leanh::lean_obj_tag(v___x_4937_) == 0 {
                    v_a_4938_ = leanh::lean_ctor_get(v___x_4937_, 0);
                    v_isSharedCheck_4953_ = (!leanh::lean_is_exclusive(v___x_4937_)) as u8;
                    if v_isSharedCheck_4953_ == 0 {
                        v___x_4940_ = v___x_4937_;
                        v_isShared_4941_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4938_);
                        leanh::lean_dec(v___x_4937_);
                        v___x_4940_ = leanh::lean_box(0);
                        v_isShared_4941_ = v_isSharedCheck_4953_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4954_ = leanh::lean_ctor_get(v___x_4937_, 0);
                    v_isSharedCheck_4961_ = (!leanh::lean_is_exclusive(v___x_4937_)) as u8;
                    if v_isSharedCheck_4961_ == 0 {
                        v___x_4956_ = v___x_4937_;
                        v_isShared_4957_ = v_isSharedCheck_4961_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4954_);
                        leanh::lean_dec(v___x_4937_);
                        v___x_4956_ = leanh::lean_box(0);
                        v_isShared_4957_ = v_isSharedCheck_4961_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_idempotentInst_x3f_4942_ = leanh::lean_ctor_get(v_a_4938_, 6);
                leanh::lean_inc(v_idempotentInst_x3f_4942_);
                leanh::lean_dec(v_a_4938_);
                if leanh::lean_obj_tag(v_idempotentInst_x3f_4942_) == 0 {
                    v___x_4943_ = 0;
                    v___x_4944_ = leanh::lean_box((v___x_4943_) as usize);
                    if v_isShared_4941_ == 0 {
                        leanh::lean_ctor_set(v___x_4940_, 0, v___x_4944_);
                        v___x_4946_ = v___x_4940_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4944_);
                        v___x_4946_ = v_reuseFailAlloc_4947_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_idempotentInst_x3f_4942_, 1);
                    v___x_4948_ = 1;
                    v___x_4949_ = leanh::lean_box((v___x_4948_) as usize);
                    if v_isShared_4941_ == 0 {
                        leanh::lean_ctor_set(v___x_4940_, 0, v___x_4949_);
                        v___x_4951_ = v___x_4940_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4952_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4949_);
                        v___x_4951_ = v_reuseFailAlloc_4952_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4946_;
            }
            3 => {
                return v___x_4951_;
            }
            4 => {
                if v_isShared_4957_ == 0 {
                    v___x_4959_ = v___x_4956_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
                    v___x_4959_ = v_reuseFailAlloc_4960_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_isIdempotent___boxed(
    mut v_a_4962_: *mut leanh::LeanObject,
    mut v_a_4963_: *mut leanh::LeanObject,
    mut v_a_4964_: *mut leanh::LeanObject,
    mut v_a_4965_: *mut leanh::LeanObject,
    mut v_a_4966_: *mut leanh::LeanObject,
    mut v_a_4967_: *mut leanh::LeanObject,
    mut v_a_4968_: *mut leanh::LeanObject,
    mut v_a_4969_: *mut leanh::LeanObject,
    mut v_a_4970_: *mut leanh::LeanObject,
    mut v_a_4971_: *mut leanh::LeanObject,
    mut v_a_4972_: *mut leanh::LeanObject,
    mut v_a_4973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4974_ = l_Lean_Meta_Grind_AC_isIdempotent(
        v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_,
        v_a_4970_, v_a_4971_, v_a_4972_,
    );
    leanh::lean_dec(v_a_4972_);
    leanh::lean_dec_ref(v_a_4971_);
    leanh::lean_dec(v_a_4970_);
    leanh::lean_dec_ref(v_a_4969_);
    leanh::lean_dec(v_a_4968_);
    leanh::lean_dec_ref(v_a_4967_);
    leanh::lean_dec(v_a_4966_);
    leanh::lean_dec_ref(v_a_4965_);
    leanh::lean_dec(v_a_4964_);
    leanh::lean_dec(v_a_4963_);
    leanh::lean_dec(v_a_4962_);
    return v_res_4974_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc =
        _init_l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_AC_Util_0__Lean_Meta_Grind_AC_notAssoc,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Util(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
}