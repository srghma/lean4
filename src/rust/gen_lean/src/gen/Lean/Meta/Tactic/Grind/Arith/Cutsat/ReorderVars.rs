// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.ReorderVars
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_grind_cutsat_assert_le, lean_int_dec_lt, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_abs, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr,
    lean_nat_sub, lean_nat_to_int, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt,
    lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_range};
use crate::r#gen::Init::Data::Int::Linear::l_Int_Linear_instBEqPoly_beq;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Ord::Basic::l_instDecidableEqOrdering;
use crate::r#gen::Init::Data::Range::Basic::l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_isEmpty___redArg,
    l_Lean_PersistentArray_push___redArg, l_Lean_PersistentArray_toArray___redArg,
    l_Lean_instInhabitedPersistentArray_default, l_Lean_instInhabitedPersistentArrayNode_default,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::DvdCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr,
    l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert, l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::EqCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr,
    l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert,
    l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm, l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Inv::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv,
    l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::LeCnstr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr,
    l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg,
    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0_value
)
    as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value:
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
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value:
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
    m_data: [108, 105, 97, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value:
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
    m_data: [115, 101, 97, 114, 99, 104, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value:
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
    m_data: [114, 101, 111, 114, 100, 101, 114, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__1_value)
            as *mut leanh::LeanObject,
        15947788021050471391 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__2_value)
            as *mut leanh::LeanObject,
        5637236024813792860 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__3_value)
            as *mut leanh::LeanObject,
        12441483040187581015 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__4_value)
            as *mut leanh::LeanObject,
        8688716430328349044 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__5_value)
            as *mut leanh::LeanObject,
        3226274256350322668 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__7_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value:
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
    m_data: [111, 108, 100, 50, 110, 101, 119, 58, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value:
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
    m_data: [110, 101, 119, 50, 111, 108, 100, 58, 32, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(
    mut v_a_3554_: *mut leanh::LeanObject,
    mut v_x_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: u8 = 0;
    let mut v_v_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxLowerCoeff_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxUpperCoeff_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDvdCoeff_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3574_: u8 = 0;
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3579_: u8 = 0;
    let mut v_unused_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3558_ = leanh::lean_box(0);
                v___x_3563_ = lean_array_get_size(v_a_3556_);
                v___x_3564_ = lean_nat_dec_lt(v_x_3555_, v___x_3563_);
                if v___x_3564_ == 0 {
                    leanh::lean_dec(v_a_3554_);
                    v___y_3560_ = v_a_3556_;
                    state = 1;
                    continue;
                } else {
                    v_v_3565_ = lean_array_fget(v_a_3556_, v_x_3555_);
                    v_maxLowerCoeff_3566_ = leanh::lean_ctor_get(v_v_3565_, 0);
                    v_xs_x27_3567_ = lean_array_fset(v_a_3556_, v_x_3555_, v___x_3558_);
                    v___x_3581_ = lean_nat_dec_le(v_a_3554_, v_maxLowerCoeff_3566_);
                    if v___x_3581_ == 0 {
                        v___y_3569_ = v_a_3554_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_3554_);
                        leanh::lean_inc(v_maxLowerCoeff_3566_);
                        v___y_3569_ = v_maxLowerCoeff_3566_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3561_, 0, v___x_3558_);
                leanh::lean_ctor_set(v___x_3561_, 1, v___y_3560_);
                v___x_3562_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3562_, 0, v___x_3561_);
                return v___x_3562_;
            }
            2 => {
                v_maxUpperCoeff_3570_ = leanh::lean_ctor_get(v_v_3565_, 1);
                v_maxDvdCoeff_3571_ = leanh::lean_ctor_get(v_v_3565_, 2);
                v_isSharedCheck_3579_ = (!leanh::lean_is_exclusive(v_v_3565_)) as u8;
                if v_isSharedCheck_3579_ == 0 {
                    v_unused_3580_ = leanh::lean_ctor_get(v_v_3565_, 0);
                    leanh::lean_dec(v_unused_3580_);
                    v___x_3573_ = v_v_3565_;
                    v_isShared_3574_ = v_isSharedCheck_3579_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_maxDvdCoeff_3571_);
                    leanh::lean_inc(v_maxUpperCoeff_3570_);
                    leanh::lean_dec(v_v_3565_);
                    v___x_3573_ = leanh::lean_box(0);
                    v_isShared_3574_ = v_isSharedCheck_3579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3574_ == 0 {
                    leanh::lean_ctor_set(v___x_3573_, 0, v___y_3569_);
                    v___x_3576_ = v___x_3573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3578_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 0, v___y_3569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 1, v_maxUpperCoeff_3570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3578_, 2, v_maxDvdCoeff_3571_);
                    v___x_3576_ = v_reuseFailAlloc_3578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3577_ = lean_array_fset(v_xs_x27_3567_, v_x_3555_, v___x_3576_);
                v___y_3560_ = v___x_3577_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg___boxed(
    mut v_a_3582_: *mut leanh::LeanObject,
    mut v_x_3583_: *mut leanh::LeanObject,
    mut v_a_3584_: *mut leanh::LeanObject,
    mut v_a_3585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3586_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_3582_, v_x_3583_, v_a_3584_);
    leanh::lean_dec(v_x_3583_);
    return v_res_3586_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(
    mut v_a_3587_: *mut leanh::LeanObject,
    mut v_x_3588_: *mut leanh::LeanObject,
    mut v_a_3589_: *mut leanh::LeanObject,
    mut v_a_3590_: *mut leanh::LeanObject,
    mut v_a_3591_: *mut leanh::LeanObject,
    mut v_a_3592_: *mut leanh::LeanObject,
    mut v_a_3593_: *mut leanh::LeanObject,
    mut v_a_3594_: *mut leanh::LeanObject,
    mut v_a_3595_: *mut leanh::LeanObject,
    mut v_a_3596_: *mut leanh::LeanObject,
    mut v_a_3597_: *mut leanh::LeanObject,
    mut v_a_3598_: *mut leanh::LeanObject,
    mut v_a_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3601_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v_a_3587_, v_x_3588_, v_a_3589_);
    return v___x_3601_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___boxed(
    mut v_a_3602_: *mut leanh::LeanObject,
    mut v_x_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
    mut v_a_3605_: *mut leanh::LeanObject,
    mut v_a_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
    mut v_a_3609_: *mut leanh::LeanObject,
    mut v_a_3610_: *mut leanh::LeanObject,
    mut v_a_3611_: *mut leanh::LeanObject,
    mut v_a_3612_: *mut leanh::LeanObject,
    mut v_a_3613_: *mut leanh::LeanObject,
    mut v_a_3614_: *mut leanh::LeanObject,
    mut v_a_3615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower(v_a_3602_, v_x_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_, v_a_3614_);
    leanh::lean_dec(v_a_3614_);
    leanh::lean_dec_ref(v_a_3613_);
    leanh::lean_dec(v_a_3612_);
    leanh::lean_dec_ref(v_a_3611_);
    leanh::lean_dec(v_a_3610_);
    leanh::lean_dec_ref(v_a_3609_);
    leanh::lean_dec(v_a_3608_);
    leanh::lean_dec_ref(v_a_3607_);
    leanh::lean_dec(v_a_3606_);
    leanh::lean_dec(v_a_3605_);
    leanh::lean_dec(v_x_3603_);
    return v_res_3616_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(
    mut v_a_3617_: *mut leanh::LeanObject,
    mut v_x_3618_: *mut leanh::LeanObject,
    mut v_a_3619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: u8 = 0;
    let mut v_v_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxLowerCoeff_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxUpperCoeff_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDvdCoeff_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3634_: u8 = 0;
    let mut v_xs_x27_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v_isSharedCheck_3643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3621_ = leanh::lean_box(0);
                v___x_3626_ = lean_array_get_size(v_a_3619_);
                v___x_3627_ = lean_nat_dec_lt(v_x_3618_, v___x_3626_);
                if v___x_3627_ == 0 {
                    leanh::lean_dec(v_a_3617_);
                    v___y_3623_ = v_a_3619_;
                    state = 1;
                    continue;
                } else {
                    v_v_3628_ = lean_array_fget(v_a_3619_, v_x_3618_);
                    v_maxLowerCoeff_3629_ = leanh::lean_ctor_get(v_v_3628_, 0);
                    v_maxUpperCoeff_3630_ = leanh::lean_ctor_get(v_v_3628_, 1);
                    v_maxDvdCoeff_3631_ = leanh::lean_ctor_get(v_v_3628_, 2);
                    v_isSharedCheck_3643_ = (!leanh::lean_is_exclusive(v_v_3628_)) as u8;
                    if v_isSharedCheck_3643_ == 0 {
                        v___x_3633_ = v_v_3628_;
                        v_isShared_3634_ = v_isSharedCheck_3643_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_maxDvdCoeff_3631_);
                        leanh::lean_inc(v_maxUpperCoeff_3630_);
                        leanh::lean_inc(v_maxLowerCoeff_3629_);
                        leanh::lean_dec(v_v_3628_);
                        v___x_3633_ = leanh::lean_box(0);
                        v_isShared_3634_ = v_isSharedCheck_3643_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3624_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3624_, 0, v___x_3621_);
                leanh::lean_ctor_set(v___x_3624_, 1, v___y_3623_);
                v___x_3625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3625_, 0, v___x_3624_);
                return v___x_3625_;
            }
            2 => {
                v_xs_x27_3635_ = lean_array_fset(v_a_3619_, v_x_3618_, v___x_3621_);
                v___x_3642_ = lean_nat_dec_le(v_a_3617_, v_maxUpperCoeff_3630_);
                if v___x_3642_ == 0 {
                    leanh::lean_dec(v_maxUpperCoeff_3630_);
                    v___y_3637_ = v_a_3617_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_a_3617_);
                    v___y_3637_ = v_maxUpperCoeff_3630_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3634_ == 0 {
                    leanh::lean_ctor_set(v___x_3633_, 1, v___y_3637_);
                    v___x_3639_ = v___x_3633_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3641_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_maxLowerCoeff_3629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 1, v___y_3637_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 2, v_maxDvdCoeff_3631_);
                    v___x_3639_ = v_reuseFailAlloc_3641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3640_ = lean_array_fset(v_xs_x27_3635_, v_x_3618_, v___x_3639_);
                v___y_3623_ = v___x_3640_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg___boxed(
    mut v_a_3644_: *mut leanh::LeanObject,
    mut v_x_3645_: *mut leanh::LeanObject,
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v_a_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_3644_, v_x_3645_, v_a_3646_);
    leanh::lean_dec(v_x_3645_);
    return v_res_3648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(
    mut v_a_3649_: *mut leanh::LeanObject,
    mut v_x_3650_: *mut leanh::LeanObject,
    mut v_a_3651_: *mut leanh::LeanObject,
    mut v_a_3652_: *mut leanh::LeanObject,
    mut v_a_3653_: *mut leanh::LeanObject,
    mut v_a_3654_: *mut leanh::LeanObject,
    mut v_a_3655_: *mut leanh::LeanObject,
    mut v_a_3656_: *mut leanh::LeanObject,
    mut v_a_3657_: *mut leanh::LeanObject,
    mut v_a_3658_: *mut leanh::LeanObject,
    mut v_a_3659_: *mut leanh::LeanObject,
    mut v_a_3660_: *mut leanh::LeanObject,
    mut v_a_3661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v_a_3649_, v_x_3650_, v_a_3651_);
    return v___x_3663_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___boxed(
    mut v_a_3664_: *mut leanh::LeanObject,
    mut v_x_3665_: *mut leanh::LeanObject,
    mut v_a_3666_: *mut leanh::LeanObject,
    mut v_a_3667_: *mut leanh::LeanObject,
    mut v_a_3668_: *mut leanh::LeanObject,
    mut v_a_3669_: *mut leanh::LeanObject,
    mut v_a_3670_: *mut leanh::LeanObject,
    mut v_a_3671_: *mut leanh::LeanObject,
    mut v_a_3672_: *mut leanh::LeanObject,
    mut v_a_3673_: *mut leanh::LeanObject,
    mut v_a_3674_: *mut leanh::LeanObject,
    mut v_a_3675_: *mut leanh::LeanObject,
    mut v_a_3676_: *mut leanh::LeanObject,
    mut v_a_3677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper(v_a_3664_, v_x_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_);
    leanh::lean_dec(v_a_3676_);
    leanh::lean_dec_ref(v_a_3675_);
    leanh::lean_dec(v_a_3674_);
    leanh::lean_dec_ref(v_a_3673_);
    leanh::lean_dec(v_a_3672_);
    leanh::lean_dec_ref(v_a_3671_);
    leanh::lean_dec(v_a_3670_);
    leanh::lean_dec_ref(v_a_3669_);
    leanh::lean_dec(v_a_3668_);
    leanh::lean_dec(v_a_3667_);
    leanh::lean_dec(v_x_3665_);
    return v_res_3678_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3679_ = leanh::lean_unsigned_to_nat(0);
    v___x_3680_ = lean_nat_to_int(v___x_3679_);
    return v___x_3680_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(
    mut v_a_3681_: *mut leanh::LeanObject,
    mut v_x_3682_: *mut leanh::LeanObject,
    mut v_a_3683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: u8 = 0;
    v___x_3685_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___closed__0);
    v___x_3686_ = lean_int_dec_lt(v_a_3681_, v___x_3685_);
    if v___x_3686_ == 0 {
        let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3687_ = lean_nat_abs(v_a_3681_);
        v___x_3688_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateUpper___redArg(v___x_3687_, v_x_3682_, v_a_3683_);
        return v___x_3688_;
    } else {
        let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3689_ = lean_nat_abs(v_a_3681_);
        v___x_3690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateLower___redArg(v___x_3689_, v_x_3682_, v_a_3683_);
        return v___x_3690_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg___boxed(
    mut v_a_3691_: *mut leanh::LeanObject,
    mut v_x_3692_: *mut leanh::LeanObject,
    mut v_a_3693_: *mut leanh::LeanObject,
    mut v_a_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_3691_, v_x_3692_, v_a_3693_);
    leanh::lean_dec(v_x_3692_);
    leanh::lean_dec(v_a_3691_);
    return v_res_3695_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(
    mut v_a_3696_: *mut leanh::LeanObject,
    mut v_x_3697_: *mut leanh::LeanObject,
    mut v_a_3698_: *mut leanh::LeanObject,
    mut v_a_3699_: *mut leanh::LeanObject,
    mut v_a_3700_: *mut leanh::LeanObject,
    mut v_a_3701_: *mut leanh::LeanObject,
    mut v_a_3702_: *mut leanh::LeanObject,
    mut v_a_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
    mut v_a_3705_: *mut leanh::LeanObject,
    mut v_a_3706_: *mut leanh::LeanObject,
    mut v_a_3707_: *mut leanh::LeanObject,
    mut v_a_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3710_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_a_3696_, v_x_3697_, v_a_3698_);
    return v___x_3710_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___boxed(
    mut v_a_3711_: *mut leanh::LeanObject,
    mut v_x_3712_: *mut leanh::LeanObject,
    mut v_a_3713_: *mut leanh::LeanObject,
    mut v_a_3714_: *mut leanh::LeanObject,
    mut v_a_3715_: *mut leanh::LeanObject,
    mut v_a_3716_: *mut leanh::LeanObject,
    mut v_a_3717_: *mut leanh::LeanObject,
    mut v_a_3718_: *mut leanh::LeanObject,
    mut v_a_3719_: *mut leanh::LeanObject,
    mut v_a_3720_: *mut leanh::LeanObject,
    mut v_a_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
    mut v_a_3723_: *mut leanh::LeanObject,
    mut v_a_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff(v_a_3711_, v_x_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_);
    leanh::lean_dec(v_a_3723_);
    leanh::lean_dec_ref(v_a_3722_);
    leanh::lean_dec(v_a_3721_);
    leanh::lean_dec_ref(v_a_3720_);
    leanh::lean_dec(v_a_3719_);
    leanh::lean_dec_ref(v_a_3718_);
    leanh::lean_dec(v_a_3717_);
    leanh::lean_dec_ref(v_a_3716_);
    leanh::lean_dec(v_a_3715_);
    leanh::lean_dec(v_a_3714_);
    leanh::lean_dec(v_x_3712_);
    leanh::lean_dec(v_a_3711_);
    return v_res_3725_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(
    mut v_a_3726_: *mut leanh::LeanObject,
    mut v_x_3727_: *mut leanh::LeanObject,
    mut v_a_3728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v_v_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxLowerCoeff_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxUpperCoeff_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDvdCoeff_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3750_: u8 = 0;
    let mut v_unused_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3730_ = leanh::lean_box(0);
                v___x_3735_ = lean_array_get_size(v_a_3728_);
                v___x_3736_ = lean_nat_dec_lt(v_x_3727_, v___x_3735_);
                if v___x_3736_ == 0 {
                    leanh::lean_dec(v_a_3726_);
                    v___y_3732_ = v_a_3728_;
                    state = 1;
                    continue;
                } else {
                    v_v_3737_ = lean_array_fget(v_a_3728_, v_x_3727_);
                    v_maxLowerCoeff_3738_ = leanh::lean_ctor_get(v_v_3737_, 0);
                    v_maxUpperCoeff_3739_ = leanh::lean_ctor_get(v_v_3737_, 1);
                    v_maxDvdCoeff_3740_ = leanh::lean_ctor_get(v_v_3737_, 2);
                    v_xs_x27_3741_ = lean_array_fset(v_a_3728_, v_x_3727_, v___x_3730_);
                    v___x_3742_ = lean_nat_dec_le(v_a_3726_, v_maxDvdCoeff_3740_);
                    if v___x_3742_ == 0 {
                        leanh::lean_inc(v_maxUpperCoeff_3739_);
                        leanh::lean_inc(v_maxLowerCoeff_3738_);
                        v_isSharedCheck_3750_ = (!leanh::lean_is_exclusive(v_v_3737_)) as u8;
                        if v_isSharedCheck_3750_ == 0 {
                            v_unused_3751_ = leanh::lean_ctor_get(v_v_3737_, 2);
                            leanh::lean_dec(v_unused_3751_);
                            v_unused_3752_ = leanh::lean_ctor_get(v_v_3737_, 1);
                            leanh::lean_dec(v_unused_3752_);
                            v_unused_3753_ = leanh::lean_ctor_get(v_v_3737_, 0);
                            leanh::lean_dec(v_unused_3753_);
                            v___x_3744_ = v_v_3737_;
                            v_isShared_3745_ = v_isSharedCheck_3750_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_v_3737_);
                            v___x_3744_ = leanh::lean_box(0);
                            v_isShared_3745_ = v_isSharedCheck_3750_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3726_);
                        v___x_3754_ = lean_array_fset(v_xs_x27_3741_, v_x_3727_, v_v_3737_);
                        v___y_3732_ = v___x_3754_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3733_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3733_, 0, v___x_3730_);
                leanh::lean_ctor_set(v___x_3733_, 1, v___y_3732_);
                v___x_3734_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3734_, 0, v___x_3733_);
                return v___x_3734_;
            }
            2 => {
                if v_isShared_3745_ == 0 {
                    leanh::lean_ctor_set(v___x_3744_, 2, v_a_3726_);
                    v___x_3747_ = v___x_3744_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3749_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_maxLowerCoeff_3738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_maxUpperCoeff_3739_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_a_3726_);
                    v___x_3747_ = v_reuseFailAlloc_3749_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3748_ = lean_array_fset(v_xs_x27_3741_, v_x_3727_, v___x_3747_);
                v___y_3732_ = v___x_3748_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg___boxed(
    mut v_a_3755_: *mut leanh::LeanObject,
    mut v_x_3756_: *mut leanh::LeanObject,
    mut v_a_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_3755_, v_x_3756_, v_a_3757_);
    leanh::lean_dec(v_x_3756_);
    return v_res_3759_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(
    mut v_a_3760_: *mut leanh::LeanObject,
    mut v_x_3761_: *mut leanh::LeanObject,
    mut v_a_3762_: *mut leanh::LeanObject,
    mut v_a_3763_: *mut leanh::LeanObject,
    mut v_a_3764_: *mut leanh::LeanObject,
    mut v_a_3765_: *mut leanh::LeanObject,
    mut v_a_3766_: *mut leanh::LeanObject,
    mut v_a_3767_: *mut leanh::LeanObject,
    mut v_a_3768_: *mut leanh::LeanObject,
    mut v_a_3769_: *mut leanh::LeanObject,
    mut v_a_3770_: *mut leanh::LeanObject,
    mut v_a_3771_: *mut leanh::LeanObject,
    mut v_a_3772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v_a_3760_, v_x_3761_, v_a_3762_);
    return v___x_3774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___boxed(
    mut v_a_3775_: *mut leanh::LeanObject,
    mut v_x_3776_: *mut leanh::LeanObject,
    mut v_a_3777_: *mut leanh::LeanObject,
    mut v_a_3778_: *mut leanh::LeanObject,
    mut v_a_3779_: *mut leanh::LeanObject,
    mut v_a_3780_: *mut leanh::LeanObject,
    mut v_a_3781_: *mut leanh::LeanObject,
    mut v_a_3782_: *mut leanh::LeanObject,
    mut v_a_3783_: *mut leanh::LeanObject,
    mut v_a_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
    mut v_a_3788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3789_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd(v_a_3775_, v_x_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
    leanh::lean_dec(v_a_3787_);
    leanh::lean_dec_ref(v_a_3786_);
    leanh::lean_dec(v_a_3785_);
    leanh::lean_dec_ref(v_a_3784_);
    leanh::lean_dec(v_a_3783_);
    leanh::lean_dec_ref(v_a_3782_);
    leanh::lean_dec(v_a_3781_);
    leanh::lean_dec_ref(v_a_3780_);
    leanh::lean_dec(v_a_3779_);
    leanh::lean_dec(v_a_3778_);
    leanh::lean_dec(v_x_3776_);
    return v_res_3789_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(
    mut v_a_3790_: *mut leanh::LeanObject,
    mut v_a_3791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3795_: u8 = 0;
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3801_: u8 = 0;
    let mut v_unused_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3790_) == 0 {
                    v_isSharedCheck_3801_ = (!leanh::lean_is_exclusive(v_a_3790_)) as u8;
                    if v_isSharedCheck_3801_ == 0 {
                        v_unused_3802_ = leanh::lean_ctor_get(v_a_3790_, 0);
                        leanh::lean_dec(v_unused_3802_);
                        v___x_3794_ = v_a_3790_;
                        v_isShared_3795_ = v_isSharedCheck_3801_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_3790_);
                        v___x_3794_ = leanh::lean_box(0);
                        v_isShared_3795_ = v_isSharedCheck_3801_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_3803_ = leanh::lean_ctor_get(v_a_3790_, 0);
                    leanh::lean_inc(v_k_3803_);
                    v_v_3804_ = leanh::lean_ctor_get(v_a_3790_, 1);
                    leanh::lean_inc(v_v_3804_);
                    v_p_3805_ = leanh::lean_ctor_get(v_a_3790_, 2);
                    leanh::lean_inc_ref(v_p_3805_);
                    leanh::lean_dec_ref_known(v_a_3790_, 3);
                    v___x_3806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateVarCoeff___redArg(v_k_3803_, v_v_3804_, v_a_3791_);
                    leanh::lean_dec(v_v_3804_);
                    leanh::lean_dec(v_k_3803_);
                    v_a_3807_ = leanh::lean_ctor_get(v___x_3806_, 0);
                    leanh::lean_inc(v_a_3807_);
                    leanh::lean_dec_ref(v___x_3806_);
                    v_snd_3808_ = leanh::lean_ctor_get(v_a_3807_, 1);
                    leanh::lean_inc(v_snd_3808_);
                    leanh::lean_dec(v_a_3807_);
                    v_a_3790_ = v_p_3805_;
                    v_a_3791_ = v_snd_3808_;
                    state = 0;
                    continue;
                }
            }
            1 => {
                v___x_3796_ = leanh::lean_box(0);
                v___x_3797_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3797_, 0, v___x_3796_);
                leanh::lean_ctor_set(v___x_3797_, 1, v_a_3791_);
                if v_isShared_3795_ == 0 {
                    leanh::lean_ctor_set(v___x_3794_, 0, v___x_3797_);
                    v___x_3799_ = v___x_3794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3800_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3797_);
                    v___x_3799_ = v_reuseFailAlloc_3800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3799_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg___boxed(
    mut v_a_3810_: *mut leanh::LeanObject,
    mut v_a_3811_: *mut leanh::LeanObject,
    mut v_a_3812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_3810_, v_a_3811_);
    return v_res_3813_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(
    mut v_a_3814_: *mut leanh::LeanObject,
    mut v_a_3815_: *mut leanh::LeanObject,
    mut v_a_3816_: *mut leanh::LeanObject,
    mut v_a_3817_: *mut leanh::LeanObject,
    mut v_a_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
    mut v_a_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_a_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
    mut v_a_3824_: *mut leanh::LeanObject,
    mut v_a_3825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_a_3814_, v_a_3815_);
    return v___x_3827_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___boxed(
    mut v_a_3828_: *mut leanh::LeanObject,
    mut v_a_3829_: *mut leanh::LeanObject,
    mut v_a_3830_: *mut leanh::LeanObject,
    mut v_a_3831_: *mut leanh::LeanObject,
    mut v_a_3832_: *mut leanh::LeanObject,
    mut v_a_3833_: *mut leanh::LeanObject,
    mut v_a_3834_: *mut leanh::LeanObject,
    mut v_a_3835_: *mut leanh::LeanObject,
    mut v_a_3836_: *mut leanh::LeanObject,
    mut v_a_3837_: *mut leanh::LeanObject,
    mut v_a_3838_: *mut leanh::LeanObject,
    mut v_a_3839_: *mut leanh::LeanObject,
    mut v_a_3840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3841_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly(v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_);
    leanh::lean_dec(v_a_3839_);
    leanh::lean_dec_ref(v_a_3838_);
    leanh::lean_dec(v_a_3837_);
    leanh::lean_dec_ref(v_a_3836_);
    leanh::lean_dec(v_a_3835_);
    leanh::lean_dec_ref(v_a_3834_);
    leanh::lean_dec(v_a_3833_);
    leanh::lean_dec_ref(v_a_3832_);
    leanh::lean_dec(v_a_3831_);
    leanh::lean_dec(v_a_3830_);
    return v_res_3841_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(
    mut v_as_3845_: *mut leanh::LeanObject,
    mut v_sz_3846_: usize,
    mut v_i_3847_: usize,
    mut v_b_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3851_: u8 = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: usize = 0;
    let mut v___x_3861_: usize = 0;
    let mut v_a_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3851_ = lean_usize_dec_lt(v_i_3847_, v_sz_3846_);
                if v___x_3851_ == 0 {
                    v___x_3852_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3852_, 0, v_b_3848_);
                    leanh::lean_ctor_set(v___x_3852_, 1, v___y_3849_);
                    v___x_3853_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3853_, 0, v___x_3852_);
                    return v___x_3853_;
                } else {
                    leanh::lean_dec_ref(v_b_3848_);
                    v_a_3854_ = lean_array_uget_borrowed(v_as_3845_, v_i_3847_);
                    v_p_3855_ = leanh::lean_ctor_get(v_a_3854_, 0);
                    leanh::lean_inc_ref(v_p_3855_);
                    v___x_3856_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_3855_, v___y_3849_);
                    if leanh::lean_obj_tag(v___x_3856_) == 0 {
                        v_a_3857_ = leanh::lean_ctor_get(v___x_3856_, 0);
                        leanh::lean_inc(v_a_3857_);
                        leanh::lean_dec_ref_known(v___x_3856_, 1);
                        v_snd_3858_ = leanh::lean_ctor_get(v_a_3857_, 1);
                        leanh::lean_inc(v_snd_3858_);
                        leanh::lean_dec(v_a_3857_);
                        v___x_3859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0;
                        v___x_3860_ = 1usize;
                        v___x_3861_ = lean_usize_add(v_i_3847_, v___x_3860_);
                        v_i_3847_ = v___x_3861_;
                        v_b_3848_ = v___x_3859_;
                        v___y_3849_ = v_snd_3858_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3863_ = leanh::lean_ctor_get(v___x_3856_, 0);
                        v_isSharedCheck_3870_ =
                            (!leanh::lean_is_exclusive(v___x_3856_)) as u8;
                        if v_isSharedCheck_3870_ == 0 {
                            v___x_3865_ = v___x_3856_;
                            v_isShared_3866_ = v_isSharedCheck_3870_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3863_);
                            leanh::lean_dec(v___x_3856_);
                            v___x_3865_ = leanh::lean_box(0);
                            v_isShared_3866_ = v_isSharedCheck_3870_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3866_ == 0 {
                    v___x_3868_ = v___x_3865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
                    v___x_3868_ = v_reuseFailAlloc_3869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_as_3871_: *mut leanh::LeanObject,
    mut v_sz_3872_: *mut leanh::LeanObject,
    mut v_i_3873_: *mut leanh::LeanObject,
    mut v_b_3874_: *mut leanh::LeanObject,
    mut v___y_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3877_: usize = 0;
    let mut v_i_boxed_3878_: usize = 0;
    let mut v_res_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3877_ = leanh::lean_unbox_usize(v_sz_3872_);
    leanh::lean_dec(v_sz_3872_);
    v_i_boxed_3878_ = leanh::lean_unbox_usize(v_i_3873_);
    leanh::lean_dec(v_i_3873_);
    v_res_3879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_3871_, v_sz_boxed_3877_, v_i_boxed_3878_, v_b_3874_, v___y_3875_);
    leanh::lean_dec_ref(v_as_3871_);
    return v_res_3879_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(
    mut v_as_3880_: *mut leanh::LeanObject,
    mut v_sz_3881_: usize,
    mut v_i_3882_: usize,
    mut v_b_3883_: *mut leanh::LeanObject,
    mut v___y_3884_: *mut leanh::LeanObject,
    mut v___y_3885_: *mut leanh::LeanObject,
    mut v___y_3886_: *mut leanh::LeanObject,
    mut v___y_3887_: *mut leanh::LeanObject,
    mut v___y_3888_: *mut leanh::LeanObject,
    mut v___y_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
    mut v___y_3892_: *mut leanh::LeanObject,
    mut v___y_3893_: *mut leanh::LeanObject,
    mut v___y_3894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3896_: u8 = 0;
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: usize = 0;
    let mut v___x_3906_: usize = 0;
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3911_: u8 = 0;
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3896_ = lean_usize_dec_lt(v_i_3882_, v_sz_3881_);
                if v___x_3896_ == 0 {
                    v___x_3897_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3897_, 0, v_b_3883_);
                    leanh::lean_ctor_set(v___x_3897_, 1, v___y_3884_);
                    v___x_3898_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                    return v___x_3898_;
                } else {
                    leanh::lean_dec_ref(v_b_3883_);
                    v_a_3899_ = lean_array_uget_borrowed(v_as_3880_, v_i_3882_);
                    v_p_3900_ = leanh::lean_ctor_get(v_a_3899_, 0);
                    leanh::lean_inc_ref(v_p_3900_);
                    v___x_3901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_3900_, v___y_3884_);
                    if leanh::lean_obj_tag(v___x_3901_) == 0 {
                        v_a_3902_ = leanh::lean_ctor_get(v___x_3901_, 0);
                        leanh::lean_inc(v_a_3902_);
                        leanh::lean_dec_ref_known(v___x_3901_, 1);
                        v_snd_3903_ = leanh::lean_ctor_get(v_a_3902_, 1);
                        leanh::lean_inc(v_snd_3903_);
                        leanh::lean_dec(v_a_3902_);
                        v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg___closed__0;
                        v___x_3905_ = 1usize;
                        v___x_3906_ = lean_usize_add(v_i_3882_, v___x_3905_);
                        v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_3880_, v_sz_3881_, v___x_3906_, v___x_3904_, v_snd_3903_);
                        return v___x_3907_;
                    } else {
                        v_a_3908_ = leanh::lean_ctor_get(v___x_3901_, 0);
                        v_isSharedCheck_3915_ =
                            (!leanh::lean_is_exclusive(v___x_3901_)) as u8;
                        if v_isSharedCheck_3915_ == 0 {
                            v___x_3910_ = v___x_3901_;
                            v_isShared_3911_ = v_isSharedCheck_3915_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3908_);
                            leanh::lean_dec(v___x_3901_);
                            v___x_3910_ = leanh::lean_box(0);
                            v_isShared_3911_ = v_isSharedCheck_3915_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3911_ == 0 {
                    v___x_3913_ = v___x_3910_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3914_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
                    v___x_3913_ = v_reuseFailAlloc_3914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1___boxed(
    mut v_as_3916_: *mut leanh::LeanObject,
    mut v_sz_3917_: *mut leanh::LeanObject,
    mut v_i_3918_: *mut leanh::LeanObject,
    mut v_b_3919_: *mut leanh::LeanObject,
    mut v___y_3920_: *mut leanh::LeanObject,
    mut v___y_3921_: *mut leanh::LeanObject,
    mut v___y_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
    mut v___y_3926_: *mut leanh::LeanObject,
    mut v___y_3927_: *mut leanh::LeanObject,
    mut v___y_3928_: *mut leanh::LeanObject,
    mut v___y_3929_: *mut leanh::LeanObject,
    mut v___y_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3932_: usize = 0;
    let mut v_i_boxed_3933_: usize = 0;
    let mut v_res_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3932_ = leanh::lean_unbox_usize(v_sz_3917_);
    leanh::lean_dec(v_sz_3917_);
    v_i_boxed_3933_ = leanh::lean_unbox_usize(v_i_3918_);
    leanh::lean_dec(v_i_3918_);
    v_res_3934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_as_3916_, v_sz_boxed_3932_, v_i_boxed_3933_, v_b_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
    leanh::lean_dec(v___y_3930_);
    leanh::lean_dec_ref(v___y_3929_);
    leanh::lean_dec(v___y_3928_);
    leanh::lean_dec_ref(v___y_3927_);
    leanh::lean_dec(v___y_3926_);
    leanh::lean_dec_ref(v___y_3925_);
    leanh::lean_dec(v___y_3924_);
    leanh::lean_dec_ref(v___y_3923_);
    leanh::lean_dec(v___y_3922_);
    leanh::lean_dec(v___y_3921_);
    leanh::lean_dec_ref(v_as_3916_);
    return v_res_3934_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_as_3938_: *mut leanh::LeanObject,
    mut v_sz_3939_: usize,
    mut v_i_3940_: usize,
    mut v_b_3941_: *mut leanh::LeanObject,
    mut v___y_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3944_: u8 = 0;
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: usize = 0;
    let mut v___x_3954_: usize = 0;
    let mut v_a_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3959_: u8 = 0;
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3944_ = lean_usize_dec_lt(v_i_3940_, v_sz_3939_);
                if v___x_3944_ == 0 {
                    v___x_3945_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3945_, 0, v_b_3941_);
                    leanh::lean_ctor_set(v___x_3945_, 1, v___y_3942_);
                    v___x_3946_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3946_, 0, v___x_3945_);
                    return v___x_3946_;
                } else {
                    leanh::lean_dec_ref(v_b_3941_);
                    v_a_3947_ = lean_array_uget_borrowed(v_as_3938_, v_i_3940_);
                    v_p_3948_ = leanh::lean_ctor_get(v_a_3947_, 0);
                    leanh::lean_inc_ref(v_p_3948_);
                    v___x_3949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_3948_, v___y_3942_);
                    if leanh::lean_obj_tag(v___x_3949_) == 0 {
                        v_a_3950_ = leanh::lean_ctor_get(v___x_3949_, 0);
                        leanh::lean_inc(v_a_3950_);
                        leanh::lean_dec_ref_known(v___x_3949_, 1);
                        v_snd_3951_ = leanh::lean_ctor_get(v_a_3950_, 1);
                        leanh::lean_inc(v_snd_3951_);
                        leanh::lean_dec(v_a_3950_);
                        v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0;
                        v___x_3953_ = 1usize;
                        v___x_3954_ = lean_usize_add(v_i_3940_, v___x_3953_);
                        v_i_3940_ = v___x_3954_;
                        v_b_3941_ = v___x_3952_;
                        v___y_3942_ = v_snd_3951_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3956_ = leanh::lean_ctor_get(v___x_3949_, 0);
                        v_isSharedCheck_3963_ =
                            (!leanh::lean_is_exclusive(v___x_3949_)) as u8;
                        if v_isSharedCheck_3963_ == 0 {
                            v___x_3958_ = v___x_3949_;
                            v_isShared_3959_ = v_isSharedCheck_3963_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3956_);
                            leanh::lean_dec(v___x_3949_);
                            v___x_3958_ = leanh::lean_box(0);
                            v_isShared_3959_ = v_isSharedCheck_3963_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3959_ == 0 {
                    v___x_3961_ = v___x_3958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
                    v___x_3961_ = v_reuseFailAlloc_3962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_as_3964_: *mut leanh::LeanObject,
    mut v_sz_3965_: *mut leanh::LeanObject,
    mut v_i_3966_: *mut leanh::LeanObject,
    mut v_b_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3970_: usize = 0;
    let mut v_i_boxed_3971_: usize = 0;
    let mut v_res_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3970_ = leanh::lean_unbox_usize(v_sz_3965_);
    leanh::lean_dec(v_sz_3965_);
    v_i_boxed_3971_ = leanh::lean_unbox_usize(v_i_3966_);
    leanh::lean_dec(v_i_3966_);
    v_res_3972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_3964_, v_sz_boxed_3970_, v_i_boxed_3971_, v_b_3967_, v___y_3968_);
    leanh::lean_dec_ref(v_as_3964_);
    return v_res_3972_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(
    mut v_as_3973_: *mut leanh::LeanObject,
    mut v_sz_3974_: usize,
    mut v_i_3975_: usize,
    mut v_b_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: usize = 0;
    let mut v___x_3999_: usize = 0;
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3989_ = lean_usize_dec_lt(v_i_3975_, v_sz_3974_);
                if v___x_3989_ == 0 {
                    v___x_3990_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3990_, 0, v_b_3976_);
                    leanh::lean_ctor_set(v___x_3990_, 1, v___y_3977_);
                    v___x_3991_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3991_, 0, v___x_3990_);
                    return v___x_3991_;
                } else {
                    leanh::lean_dec_ref(v_b_3976_);
                    v_a_3992_ = lean_array_uget_borrowed(v_as_3973_, v_i_3975_);
                    v_p_3993_ = leanh::lean_ctor_get(v_a_3992_, 0);
                    leanh::lean_inc_ref(v_p_3993_);
                    v___x_3994_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_visitPoly___redArg(v_p_3993_, v___y_3977_);
                    if leanh::lean_obj_tag(v___x_3994_) == 0 {
                        v_a_3995_ = leanh::lean_ctor_get(v___x_3994_, 0);
                        leanh::lean_inc(v_a_3995_);
                        leanh::lean_dec_ref_known(v___x_3994_, 1);
                        v_snd_3996_ = leanh::lean_ctor_get(v_a_3995_, 1);
                        leanh::lean_inc(v_snd_3996_);
                        leanh::lean_dec(v_a_3995_);
                        v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg___closed__0;
                        v___x_3998_ = 1usize;
                        v___x_3999_ = lean_usize_add(v_i_3975_, v___x_3998_);
                        v___x_4000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_3973_, v_sz_3974_, v___x_3999_, v___x_3997_, v_snd_3996_);
                        return v___x_4000_;
                    } else {
                        v_a_4001_ = leanh::lean_ctor_get(v___x_3994_, 0);
                        v_isSharedCheck_4008_ =
                            (!leanh::lean_is_exclusive(v___x_3994_)) as u8;
                        if v_isSharedCheck_4008_ == 0 {
                            v___x_4003_ = v___x_3994_;
                            v_isShared_4004_ = v_isSharedCheck_4008_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4001_);
                            leanh::lean_dec(v___x_3994_);
                            v___x_4003_ = leanh::lean_box(0);
                            v_isShared_4004_ = v_isSharedCheck_4008_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4004_ == 0 {
                    v___x_4006_ = v___x_4003_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4007_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
                    v___x_4006_ = v_reuseFailAlloc_4007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2___boxed(
    mut v_as_4009_: *mut leanh::LeanObject,
    mut v_sz_4010_: *mut leanh::LeanObject,
    mut v_i_4011_: *mut leanh::LeanObject,
    mut v_b_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
    mut v___y_4014_: *mut leanh::LeanObject,
    mut v___y_4015_: *mut leanh::LeanObject,
    mut v___y_4016_: *mut leanh::LeanObject,
    mut v___y_4017_: *mut leanh::LeanObject,
    mut v___y_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
    mut v___y_4023_: *mut leanh::LeanObject,
    mut v___y_4024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4025_: usize = 0;
    let mut v_i_boxed_4026_: usize = 0;
    let mut v_res_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4025_ = leanh::lean_unbox_usize(v_sz_4010_);
    leanh::lean_dec(v_sz_4010_);
    v_i_boxed_4026_ = leanh::lean_unbox_usize(v_i_4011_);
    leanh::lean_dec(v_i_4011_);
    v_res_4027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_as_4009_, v_sz_boxed_4025_, v_i_boxed_4026_, v_b_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
    leanh::lean_dec(v___y_4023_);
    leanh::lean_dec_ref(v___y_4022_);
    leanh::lean_dec(v___y_4021_);
    leanh::lean_dec_ref(v___y_4020_);
    leanh::lean_dec(v___y_4019_);
    leanh::lean_dec_ref(v___y_4018_);
    leanh::lean_dec(v___y_4017_);
    leanh::lean_dec_ref(v___y_4016_);
    leanh::lean_dec(v___y_4015_);
    leanh::lean_dec(v___y_4014_);
    leanh::lean_dec_ref(v_as_4009_);
    return v_res_4027_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(
    mut v_init_4028_: *mut leanh::LeanObject,
    mut v_n_4029_: *mut leanh::LeanObject,
    mut v_b_4030_: *mut leanh::LeanObject,
    mut v___y_4031_: *mut leanh::LeanObject,
    mut v___y_4032_: *mut leanh::LeanObject,
    mut v___y_4033_: *mut leanh::LeanObject,
    mut v___y_4034_: *mut leanh::LeanObject,
    mut v___y_4035_: *mut leanh::LeanObject,
    mut v___y_4036_: *mut leanh::LeanObject,
    mut v___y_4037_: *mut leanh::LeanObject,
    mut v___y_4038_: *mut leanh::LeanObject,
    mut v___y_4039_: *mut leanh::LeanObject,
    mut v___y_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4046_: usize = 0;
    let mut v___x_4047_: usize = 0;
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v_fst_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_unused_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v_snd_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4080_: u8 = 0;
    let mut v_unused_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v_a_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4087_: u8 = 0;
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4091_: u8 = 0;
    let mut v_vs_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4095_: usize = 0;
    let mut v___x_4096_: usize = 0;
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v_fst_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4108_: u8 = 0;
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4116_: u8 = 0;
    let mut v_unused_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v_snd_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_unused_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_a_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_4029_) == 0 {
                    v_cs_4043_ = leanh::lean_ctor_get(v_n_4029_, 0);
                    v___x_4044_ = leanh::lean_box(0);
                    v___x_4045_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4045_, 0, v___x_4044_);
                    leanh::lean_ctor_set(v___x_4045_, 1, v_b_4030_);
                    v_sz_4046_ = lean_array_size(v_cs_4043_);
                    v___x_4047_ = 0usize;
                    v___x_4048_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_4028_, v_cs_4043_, v_sz_4046_, v___x_4047_, v___x_4045_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
                    if leanh::lean_obj_tag(v___x_4048_) == 0 {
                        v_a_4049_ = leanh::lean_ctor_get(v___x_4048_, 0);
                        v_isSharedCheck_4083_ =
                            (!leanh::lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4083_ == 0 {
                            v___x_4051_ = v___x_4048_;
                            v_isShared_4052_ = v_isSharedCheck_4083_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4049_);
                            leanh::lean_dec(v___x_4048_);
                            v___x_4051_ = leanh::lean_box(0);
                            v_isShared_4052_ = v_isSharedCheck_4083_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4084_ = leanh::lean_ctor_get(v___x_4048_, 0);
                        v_isSharedCheck_4091_ =
                            (!leanh::lean_is_exclusive(v___x_4048_)) as u8;
                        if v_isSharedCheck_4091_ == 0 {
                            v___x_4086_ = v___x_4048_;
                            v_isShared_4087_ = v_isSharedCheck_4091_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4084_);
                            leanh::lean_dec(v___x_4048_);
                            v___x_4086_ = leanh::lean_box(0);
                            v_isShared_4087_ = v_isSharedCheck_4091_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_vs_4092_ = leanh::lean_ctor_get(v_n_4029_, 0);
                    v___x_4093_ = leanh::lean_box(0);
                    v___x_4094_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4094_, 0, v___x_4093_);
                    leanh::lean_ctor_set(v___x_4094_, 1, v_b_4030_);
                    v_sz_4095_ = lean_array_size(v_vs_4092_);
                    v___x_4096_ = 0usize;
                    v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2(v_vs_4092_, v_sz_4095_, v___x_4096_, v___x_4094_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
                    if leanh::lean_obj_tag(v___x_4097_) == 0 {
                        v_a_4098_ = leanh::lean_ctor_get(v___x_4097_, 0);
                        v_isSharedCheck_4132_ =
                            (!leanh::lean_is_exclusive(v___x_4097_)) as u8;
                        if v_isSharedCheck_4132_ == 0 {
                            v___x_4100_ = v___x_4097_;
                            v_isShared_4101_ = v_isSharedCheck_4132_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4098_);
                            leanh::lean_dec(v___x_4097_);
                            v___x_4100_ = leanh::lean_box(0);
                            v_isShared_4101_ = v_isSharedCheck_4132_;
                            state = 10;
                            continue;
                        }
                    } else {
                        v_a_4133_ = leanh::lean_ctor_get(v___x_4097_, 0);
                        v_isSharedCheck_4140_ =
                            (!leanh::lean_is_exclusive(v___x_4097_)) as u8;
                        if v_isSharedCheck_4140_ == 0 {
                            v___x_4135_ = v___x_4097_;
                            v_isShared_4136_ = v_isSharedCheck_4140_;
                            state = 17;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4133_);
                            leanh::lean_dec(v___x_4097_);
                            v___x_4135_ = leanh::lean_box(0);
                            v_isShared_4136_ = v_isSharedCheck_4140_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4053_ = leanh::lean_ctor_get(v_a_4049_, 0);
                leanh::lean_inc(v_fst_4053_);
                v_fst_4054_ = leanh::lean_ctor_get(v_fst_4053_, 0);
                if leanh::lean_obj_tag(v_fst_4054_) == 0 {
                    v_snd_4055_ = leanh::lean_ctor_get(v_a_4049_, 1);
                    leanh::lean_inc(v_snd_4055_);
                    leanh::lean_dec(v_a_4049_);
                    v_snd_4056_ = leanh::lean_ctor_get(v_fst_4053_, 1);
                    v_isSharedCheck_4067_ = (!leanh::lean_is_exclusive(v_fst_4053_)) as u8;
                    if v_isSharedCheck_4067_ == 0 {
                        v_unused_4068_ = leanh::lean_ctor_get(v_fst_4053_, 0);
                        leanh::lean_dec(v_unused_4068_);
                        v___x_4058_ = v_fst_4053_;
                        v_isShared_4059_ = v_isSharedCheck_4067_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4056_);
                        leanh::lean_dec(v_fst_4053_);
                        v___x_4058_ = leanh::lean_box(0);
                        v_isShared_4059_ = v_isSharedCheck_4067_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4054_);
                    v_isSharedCheck_4080_ = (!leanh::lean_is_exclusive(v_fst_4053_)) as u8;
                    if v_isSharedCheck_4080_ == 0 {
                        v_unused_4081_ = leanh::lean_ctor_get(v_fst_4053_, 1);
                        leanh::lean_dec(v_unused_4081_);
                        v_unused_4082_ = leanh::lean_ctor_get(v_fst_4053_, 0);
                        leanh::lean_dec(v_unused_4082_);
                        v___x_4070_ = v_fst_4053_;
                        v_isShared_4071_ = v_isSharedCheck_4080_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_4053_);
                        v___x_4070_ = leanh::lean_box(0);
                        v_isShared_4071_ = v_isSharedCheck_4080_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4060_, 0, v_snd_4056_);
                if v_isShared_4059_ == 0 {
                    leanh::lean_ctor_set(v___x_4058_, 1, v_snd_4055_);
                    leanh::lean_ctor_set(v___x_4058_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4058_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4060_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 1, v_snd_4055_);
                    v___x_4062_ = v_reuseFailAlloc_4066_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4052_ == 0 {
                    leanh::lean_ctor_set(v___x_4051_, 0, v___x_4062_);
                    v___x_4064_ = v___x_4051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4064_;
            }
            5 => {
                v_snd_4072_ = leanh::lean_ctor_get(v_a_4049_, 1);
                leanh::lean_inc(v_snd_4072_);
                leanh::lean_dec(v_a_4049_);
                v_val_4073_ = leanh::lean_ctor_get(v_fst_4054_, 0);
                leanh::lean_inc(v_val_4073_);
                leanh::lean_dec_ref_known(v_fst_4054_, 1);
                if v_isShared_4071_ == 0 {
                    leanh::lean_ctor_set(v___x_4070_, 1, v_snd_4072_);
                    leanh::lean_ctor_set(v___x_4070_, 0, v_val_4073_);
                    v___x_4075_ = v___x_4070_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4079_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_val_4073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4079_, 1, v_snd_4072_);
                    v___x_4075_ = v_reuseFailAlloc_4079_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4052_ == 0 {
                    leanh::lean_ctor_set(v___x_4051_, 0, v___x_4075_);
                    v___x_4077_ = v___x_4051_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4078_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4075_);
                    v___x_4077_ = v_reuseFailAlloc_4078_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4077_;
            }
            8 => {
                if v_isShared_4087_ == 0 {
                    v___x_4089_ = v___x_4086_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4090_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
                    v___x_4089_ = v_reuseFailAlloc_4090_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4089_;
            }
            10 => {
                v_fst_4102_ = leanh::lean_ctor_get(v_a_4098_, 0);
                leanh::lean_inc(v_fst_4102_);
                v_fst_4103_ = leanh::lean_ctor_get(v_fst_4102_, 0);
                if leanh::lean_obj_tag(v_fst_4103_) == 0 {
                    v_snd_4104_ = leanh::lean_ctor_get(v_a_4098_, 1);
                    leanh::lean_inc(v_snd_4104_);
                    leanh::lean_dec(v_a_4098_);
                    v_snd_4105_ = leanh::lean_ctor_get(v_fst_4102_, 1);
                    v_isSharedCheck_4116_ = (!leanh::lean_is_exclusive(v_fst_4102_)) as u8;
                    if v_isSharedCheck_4116_ == 0 {
                        v_unused_4117_ = leanh::lean_ctor_get(v_fst_4102_, 0);
                        leanh::lean_dec(v_unused_4117_);
                        v___x_4107_ = v_fst_4102_;
                        v_isShared_4108_ = v_isSharedCheck_4116_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4105_);
                        leanh::lean_dec(v_fst_4102_);
                        v___x_4107_ = leanh::lean_box(0);
                        v_isShared_4108_ = v_isSharedCheck_4116_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4103_);
                    v_isSharedCheck_4129_ = (!leanh::lean_is_exclusive(v_fst_4102_)) as u8;
                    if v_isSharedCheck_4129_ == 0 {
                        v_unused_4130_ = leanh::lean_ctor_get(v_fst_4102_, 1);
                        leanh::lean_dec(v_unused_4130_);
                        v_unused_4131_ = leanh::lean_ctor_get(v_fst_4102_, 0);
                        leanh::lean_dec(v_unused_4131_);
                        v___x_4119_ = v_fst_4102_;
                        v_isShared_4120_ = v_isSharedCheck_4129_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_4102_);
                        v___x_4119_ = leanh::lean_box(0);
                        v_isShared_4120_ = v_isSharedCheck_4129_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v___x_4109_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4109_, 0, v_snd_4105_);
                if v_isShared_4108_ == 0 {
                    leanh::lean_ctor_set(v___x_4107_, 1, v_snd_4104_);
                    leanh::lean_ctor_set(v___x_4107_, 0, v___x_4109_);
                    v___x_4111_ = v___x_4107_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4115_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4109_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4115_, 1, v_snd_4104_);
                    v___x_4111_ = v_reuseFailAlloc_4115_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4101_ == 0 {
                    leanh::lean_ctor_set(v___x_4100_, 0, v___x_4111_);
                    v___x_4113_ = v___x_4100_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4114_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___x_4111_);
                    v___x_4113_ = v_reuseFailAlloc_4114_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4113_;
            }
            14 => {
                v_snd_4121_ = leanh::lean_ctor_get(v_a_4098_, 1);
                leanh::lean_inc(v_snd_4121_);
                leanh::lean_dec(v_a_4098_);
                v_val_4122_ = leanh::lean_ctor_get(v_fst_4103_, 0);
                leanh::lean_inc(v_val_4122_);
                leanh::lean_dec_ref_known(v_fst_4103_, 1);
                if v_isShared_4120_ == 0 {
                    leanh::lean_ctor_set(v___x_4119_, 1, v_snd_4121_);
                    leanh::lean_ctor_set(v___x_4119_, 0, v_val_4122_);
                    v___x_4124_ = v___x_4119_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_val_4122_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4128_, 1, v_snd_4121_);
                    v___x_4124_ = v_reuseFailAlloc_4128_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4101_ == 0 {
                    leanh::lean_ctor_set(v___x_4100_, 0, v___x_4124_);
                    v___x_4126_ = v___x_4100_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4124_);
                    v___x_4126_ = v_reuseFailAlloc_4127_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4126_;
            }
            17 => {
                if v_isShared_4136_ == 0 {
                    v___x_4138_ = v___x_4135_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(
    mut v_init_4141_: *mut leanh::LeanObject,
    mut v_as_4142_: *mut leanh::LeanObject,
    mut v_sz_4143_: usize,
    mut v_i_4144_: usize,
    mut v_b_4145_: *mut leanh::LeanObject,
    mut v___y_4146_: *mut leanh::LeanObject,
    mut v___y_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
    mut v___y_4150_: *mut leanh::LeanObject,
    mut v___y_4151_: *mut leanh::LeanObject,
    mut v___y_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4158_: u8 = 0;
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v_a_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4170_: u8 = 0;
    let mut v_fst_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4175_: u8 = 0;
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut v_unused_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4191_: u8 = 0;
    let mut v_a_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: usize = 0;
    let mut v___x_4197_: usize = 0;
    let mut v_reuseFailAlloc_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4200_: u8 = 0;
    let mut v_unused_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4202_: u8 = 0;
    let mut v_a_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4210_: u8 = 0;
    let mut v_isSharedCheck_4211_: u8 = 0;
    let mut v_unused_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4158_ = lean_usize_dec_lt(v_i_4144_, v_sz_4143_);
                if v___x_4158_ == 0 {
                    v___x_4159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4159_, 0, v_b_4145_);
                    leanh::lean_ctor_set(v___x_4159_, 1, v___y_4146_);
                    v___x_4160_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4160_, 0, v___x_4159_);
                    return v___x_4160_;
                } else {
                    v_snd_4161_ = leanh::lean_ctor_get(v_b_4145_, 1);
                    v_isSharedCheck_4211_ = (!leanh::lean_is_exclusive(v_b_4145_)) as u8;
                    if v_isSharedCheck_4211_ == 0 {
                        v_unused_4212_ = leanh::lean_ctor_get(v_b_4145_, 0);
                        leanh::lean_dec(v_unused_4212_);
                        v___x_4163_ = v_b_4145_;
                        v_isShared_4164_ = v_isSharedCheck_4211_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4161_);
                        leanh::lean_dec(v_b_4145_);
                        v___x_4163_ = leanh::lean_box(0);
                        v_isShared_4164_ = v_isSharedCheck_4211_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4165_ = lean_array_uget_borrowed(v_as_4142_, v_i_4144_);
                leanh::lean_inc(v_snd_4161_);
                v___x_4166_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_4141_, v_a_4165_, v_snd_4161_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
                if leanh::lean_obj_tag(v___x_4166_) == 0 {
                    v_a_4167_ = leanh::lean_ctor_get(v___x_4166_, 0);
                    v_isSharedCheck_4202_ = (!leanh::lean_is_exclusive(v___x_4166_)) as u8;
                    if v_isSharedCheck_4202_ == 0 {
                        v___x_4169_ = v___x_4166_;
                        v_isShared_4170_ = v_isSharedCheck_4202_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4167_);
                        leanh::lean_dec(v___x_4166_);
                        v___x_4169_ = leanh::lean_box(0);
                        v_isShared_4170_ = v_isSharedCheck_4202_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4163_);
                    leanh::lean_dec(v_snd_4161_);
                    v_a_4203_ = leanh::lean_ctor_get(v___x_4166_, 0);
                    v_isSharedCheck_4210_ = (!leanh::lean_is_exclusive(v___x_4166_)) as u8;
                    if v_isSharedCheck_4210_ == 0 {
                        v___x_4205_ = v___x_4166_;
                        v_isShared_4206_ = v_isSharedCheck_4210_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4203_);
                        leanh::lean_dec(v___x_4166_);
                        v___x_4205_ = leanh::lean_box(0);
                        v_isShared_4206_ = v_isSharedCheck_4210_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_4171_ = leanh::lean_ctor_get(v_a_4167_, 0);
                leanh::lean_inc(v_fst_4171_);
                if leanh::lean_obj_tag(v_fst_4171_) == 0 {
                    v_snd_4172_ = leanh::lean_ctor_get(v_a_4167_, 1);
                    v_isSharedCheck_4186_ = (!leanh::lean_is_exclusive(v_a_4167_)) as u8;
                    if v_isSharedCheck_4186_ == 0 {
                        v_unused_4187_ = leanh::lean_ctor_get(v_a_4167_, 0);
                        leanh::lean_dec(v_unused_4187_);
                        v___x_4174_ = v_a_4167_;
                        v_isShared_4175_ = v_isSharedCheck_4186_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4172_);
                        leanh::lean_dec(v_a_4167_);
                        v___x_4174_ = leanh::lean_box(0);
                        v_isShared_4175_ = v_isSharedCheck_4186_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4169_);
                    leanh::lean_del_object(v___x_4163_);
                    leanh::lean_dec(v_snd_4161_);
                    v_snd_4188_ = leanh::lean_ctor_get(v_a_4167_, 1);
                    v_isSharedCheck_4200_ = (!leanh::lean_is_exclusive(v_a_4167_)) as u8;
                    if v_isSharedCheck_4200_ == 0 {
                        v_unused_4201_ = leanh::lean_ctor_get(v_a_4167_, 0);
                        leanh::lean_dec(v_unused_4201_);
                        v___x_4190_ = v_a_4167_;
                        v_isShared_4191_ = v_isSharedCheck_4200_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4188_);
                        leanh::lean_dec(v_a_4167_);
                        v___x_4190_ = leanh::lean_box(0);
                        v_isShared_4191_ = v_isSharedCheck_4200_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4176_, 0, v_fst_4171_);
                if v_isShared_4175_ == 0 {
                    leanh::lean_ctor_set(v___x_4174_, 1, v_snd_4161_);
                    leanh::lean_ctor_set(v___x_4174_, 0, v___x_4176_);
                    v___x_4178_ = v___x_4174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4185_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 1, v_snd_4161_);
                    v___x_4178_ = v_reuseFailAlloc_4185_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4164_ == 0 {
                    leanh::lean_ctor_set(v___x_4163_, 1, v_snd_4172_);
                    leanh::lean_ctor_set(v___x_4163_, 0, v___x_4178_);
                    v___x_4180_ = v___x_4163_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4178_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4184_, 1, v_snd_4172_);
                    v___x_4180_ = v_reuseFailAlloc_4184_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4170_ == 0 {
                    leanh::lean_ctor_set(v___x_4169_, 0, v___x_4180_);
                    v___x_4182_ = v___x_4169_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4183_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4180_);
                    v___x_4182_ = v_reuseFailAlloc_4183_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4182_;
            }
            7 => {
                v_a_4192_ = leanh::lean_ctor_get(v_fst_4171_, 0);
                leanh::lean_inc(v_a_4192_);
                leanh::lean_dec_ref_known(v_fst_4171_, 1);
                v___x_4193_ = leanh::lean_box(0);
                if v_isShared_4191_ == 0 {
                    leanh::lean_ctor_set(v___x_4190_, 1, v_a_4192_);
                    leanh::lean_ctor_set(v___x_4190_, 0, v___x_4193_);
                    v___x_4195_ = v___x_4190_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4199_, 1, v_a_4192_);
                    v___x_4195_ = v_reuseFailAlloc_4199_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4196_ = 1usize;
                v___x_4197_ = lean_usize_add(v_i_4144_, v___x_4196_);
                v_i_4144_ = v___x_4197_;
                v_b_4145_ = v___x_4195_;
                v___y_4146_ = v_snd_4188_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_4206_ == 0 {
                    v___x_4208_ = v___x_4205_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4203_);
                    v___x_4208_ = v_reuseFailAlloc_4209_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_init_4213_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_4214_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_4215_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_4216_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_4217_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_4218_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4219_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4220_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4221_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4222_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4223_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4224_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4225_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4226_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4227_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4228_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4229_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_4230_: usize = 0;
    let mut v_i_boxed_4231_: usize = 0;
    let mut v_res_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4230_ = leanh::lean_unbox_usize(v_sz_4215_);
    leanh::lean_dec(v_sz_4215_);
    v_i_boxed_4231_ = leanh::lean_unbox_usize(v_i_4216_);
    leanh::lean_dec(v_i_4216_);
    v_res_4232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__1(v_init_4213_, v_as_4214_, v_sz_boxed_4230_, v_i_boxed_4231_, v_b_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
    leanh::lean_dec(v___y_4228_);
    leanh::lean_dec_ref(v___y_4227_);
    leanh::lean_dec(v___y_4226_);
    leanh::lean_dec_ref(v___y_4225_);
    leanh::lean_dec(v___y_4224_);
    leanh::lean_dec_ref(v___y_4223_);
    leanh::lean_dec(v___y_4222_);
    leanh::lean_dec_ref(v___y_4221_);
    leanh::lean_dec(v___y_4220_);
    leanh::lean_dec(v___y_4219_);
    leanh::lean_dec_ref(v_as_4214_);
    return v_res_4232_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0___boxed(
    mut v_init_4233_: *mut leanh::LeanObject,
    mut v_n_4234_: *mut leanh::LeanObject,
    mut v_b_4235_: *mut leanh::LeanObject,
    mut v___y_4236_: *mut leanh::LeanObject,
    mut v___y_4237_: *mut leanh::LeanObject,
    mut v___y_4238_: *mut leanh::LeanObject,
    mut v___y_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
    mut v___y_4246_: *mut leanh::LeanObject,
    mut v___y_4247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4248_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_4233_, v_n_4234_, v_b_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
    leanh::lean_dec(v___y_4246_);
    leanh::lean_dec_ref(v___y_4245_);
    leanh::lean_dec(v___y_4244_);
    leanh::lean_dec_ref(v___y_4243_);
    leanh::lean_dec(v___y_4242_);
    leanh::lean_dec_ref(v___y_4241_);
    leanh::lean_dec(v___y_4240_);
    leanh::lean_dec_ref(v___y_4239_);
    leanh::lean_dec(v___y_4238_);
    leanh::lean_dec(v___y_4237_);
    leanh::lean_dec_ref(v_n_4234_);
    return v_res_4248_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(
    mut v_t_4249_: *mut leanh::LeanObject,
    mut v_init_4250_: *mut leanh::LeanObject,
    mut v___y_4251_: *mut leanh::LeanObject,
    mut v___y_4252_: *mut leanh::LeanObject,
    mut v___y_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
    mut v___y_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4278_: u8 = 0;
    let mut v_a_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4283_: usize = 0;
    let mut v___x_4284_: usize = 0;
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4289_: u8 = 0;
    let mut v_fst_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut v_unused_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4307_: u8 = 0;
    let mut v_a_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4311_: u8 = 0;
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4315_: u8 = 0;
    let mut v_reuseFailAlloc_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4317_: u8 = 0;
    let mut v_unused_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4322_: u8 = 0;
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4268_ = leanh::lean_ctor_get(v_t_4249_, 0);
                v_tail_4269_ = leanh::lean_ctor_get(v_t_4249_, 1);
                v___x_4270_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0(v_init_4250_, v_root_4268_, v_init_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
                if leanh::lean_obj_tag(v___x_4270_) == 0 {
                    v_a_4271_ = leanh::lean_ctor_get(v___x_4270_, 0);
                    leanh::lean_inc(v_a_4271_);
                    leanh::lean_dec_ref_known(v___x_4270_, 1);
                    v_fst_4272_ = leanh::lean_ctor_get(v_a_4271_, 0);
                    leanh::lean_inc(v_fst_4272_);
                    if leanh::lean_obj_tag(v_fst_4272_) == 0 {
                        v_snd_4273_ = leanh::lean_ctor_get(v_a_4271_, 1);
                        leanh::lean_inc(v_snd_4273_);
                        leanh::lean_dec(v_a_4271_);
                        v_a_4274_ = leanh::lean_ctor_get(v_fst_4272_, 0);
                        leanh::lean_inc(v_a_4274_);
                        leanh::lean_dec_ref_known(v_fst_4272_, 1);
                        v_b_4264_ = v_a_4274_;
                        v___y_4265_ = v_snd_4273_;
                        state = 1;
                        continue;
                    } else {
                        v_snd_4275_ = leanh::lean_ctor_get(v_a_4271_, 1);
                        v_isSharedCheck_4317_ = (!leanh::lean_is_exclusive(v_a_4271_)) as u8;
                        if v_isSharedCheck_4317_ == 0 {
                            v_unused_4318_ = leanh::lean_ctor_get(v_a_4271_, 0);
                            leanh::lean_dec(v_unused_4318_);
                            v___x_4277_ = v_a_4271_;
                            v_isShared_4278_ = v_isSharedCheck_4317_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_4275_);
                            leanh::lean_dec(v_a_4271_);
                            v___x_4277_ = leanh::lean_box(0);
                            v_isShared_4278_ = v_isSharedCheck_4317_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_4319_ = leanh::lean_ctor_get(v___x_4270_, 0);
                    v_isSharedCheck_4326_ = (!leanh::lean_is_exclusive(v___x_4270_)) as u8;
                    if v_isSharedCheck_4326_ == 0 {
                        v___x_4321_ = v___x_4270_;
                        v_isShared_4322_ = v_isSharedCheck_4326_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4319_);
                        leanh::lean_dec(v___x_4270_);
                        v___x_4321_ = leanh::lean_box(0);
                        v_isShared_4322_ = v_isSharedCheck_4326_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4266_, 0, v_b_4264_);
                leanh::lean_ctor_set(v___x_4266_, 1, v___y_4265_);
                v___x_4267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4267_, 0, v___x_4266_);
                return v___x_4267_;
            }
            2 => {
                v_a_4279_ = leanh::lean_ctor_get(v_fst_4272_, 0);
                leanh::lean_inc(v_a_4279_);
                leanh::lean_dec_ref_known(v_fst_4272_, 1);
                v___x_4280_ = leanh::lean_box(0);
                if v_isShared_4278_ == 0 {
                    leanh::lean_ctor_set(v___x_4277_, 1, v_a_4279_);
                    leanh::lean_ctor_set(v___x_4277_, 0, v___x_4280_);
                    v___x_4282_ = v___x_4277_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4316_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 0, v___x_4280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_a_4279_);
                    v___x_4282_ = v_reuseFailAlloc_4316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_4283_ = lean_array_size(v_tail_4269_);
                v___x_4284_ = 0usize;
                v___x_4285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1(v_tail_4269_, v_sz_4283_, v___x_4284_, v___x_4282_, v_snd_4275_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
                if leanh::lean_obj_tag(v___x_4285_) == 0 {
                    v_a_4286_ = leanh::lean_ctor_get(v___x_4285_, 0);
                    v_isSharedCheck_4307_ = (!leanh::lean_is_exclusive(v___x_4285_)) as u8;
                    if v_isSharedCheck_4307_ == 0 {
                        v___x_4288_ = v___x_4285_;
                        v_isShared_4289_ = v_isSharedCheck_4307_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4286_);
                        leanh::lean_dec(v___x_4285_);
                        v___x_4288_ = leanh::lean_box(0);
                        v_isShared_4289_ = v_isSharedCheck_4307_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4308_ = leanh::lean_ctor_get(v___x_4285_, 0);
                    v_isSharedCheck_4315_ = (!leanh::lean_is_exclusive(v___x_4285_)) as u8;
                    if v_isSharedCheck_4315_ == 0 {
                        v___x_4310_ = v___x_4285_;
                        v_isShared_4311_ = v_isSharedCheck_4315_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4308_);
                        leanh::lean_dec(v___x_4285_);
                        v___x_4310_ = leanh::lean_box(0);
                        v_isShared_4311_ = v_isSharedCheck_4315_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_4290_ = leanh::lean_ctor_get(v_a_4286_, 0);
                leanh::lean_inc(v_fst_4290_);
                v_fst_4291_ = leanh::lean_ctor_get(v_fst_4290_, 0);
                if leanh::lean_obj_tag(v_fst_4291_) == 0 {
                    v_snd_4292_ = leanh::lean_ctor_get(v_a_4286_, 1);
                    leanh::lean_inc(v_snd_4292_);
                    leanh::lean_dec(v_a_4286_);
                    v_snd_4293_ = leanh::lean_ctor_get(v_fst_4290_, 1);
                    v_isSharedCheck_4303_ = (!leanh::lean_is_exclusive(v_fst_4290_)) as u8;
                    if v_isSharedCheck_4303_ == 0 {
                        v_unused_4304_ = leanh::lean_ctor_get(v_fst_4290_, 0);
                        leanh::lean_dec(v_unused_4304_);
                        v___x_4295_ = v_fst_4290_;
                        v_isShared_4296_ = v_isSharedCheck_4303_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4293_);
                        leanh::lean_dec(v_fst_4290_);
                        v___x_4295_ = leanh::lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4303_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4291_);
                    leanh::lean_dec(v_fst_4290_);
                    leanh::lean_del_object(v___x_4288_);
                    v_snd_4305_ = leanh::lean_ctor_get(v_a_4286_, 1);
                    leanh::lean_inc(v_snd_4305_);
                    leanh::lean_dec(v_a_4286_);
                    v_val_4306_ = leanh::lean_ctor_get(v_fst_4291_, 0);
                    leanh::lean_inc(v_val_4306_);
                    leanh::lean_dec_ref_known(v_fst_4291_, 1);
                    v_b_4264_ = v_val_4306_;
                    v___y_4265_ = v_snd_4305_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_4296_ == 0 {
                    leanh::lean_ctor_set(v___x_4295_, 1, v_snd_4292_);
                    leanh::lean_ctor_set(v___x_4295_, 0, v_snd_4293_);
                    v___x_4298_ = v___x_4295_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_snd_4293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4302_, 1, v_snd_4292_);
                    v___x_4298_ = v_reuseFailAlloc_4302_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4289_ == 0 {
                    leanh::lean_ctor_set(v___x_4288_, 0, v___x_4298_);
                    v___x_4300_ = v___x_4288_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4301_, 0, v___x_4298_);
                    v___x_4300_ = v_reuseFailAlloc_4301_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4300_;
            }
            8 => {
                if v_isShared_4311_ == 0 {
                    v___x_4313_ = v___x_4310_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4314_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
                    v___x_4313_ = v_reuseFailAlloc_4314_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4313_;
            }
            10 => {
                if v_isShared_4322_ == 0 {
                    v___x_4324_ = v___x_4321_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4325_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
                    v___x_4324_ = v_reuseFailAlloc_4325_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0___boxed(
    mut v_t_4327_: *mut leanh::LeanObject,
    mut v_init_4328_: *mut leanh::LeanObject,
    mut v___y_4329_: *mut leanh::LeanObject,
    mut v___y_4330_: *mut leanh::LeanObject,
    mut v___y_4331_: *mut leanh::LeanObject,
    mut v___y_4332_: *mut leanh::LeanObject,
    mut v___y_4333_: *mut leanh::LeanObject,
    mut v___y_4334_: *mut leanh::LeanObject,
    mut v___y_4335_: *mut leanh::LeanObject,
    mut v___y_4336_: *mut leanh::LeanObject,
    mut v___y_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
    mut v___y_4340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4341_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v_t_4327_, v_init_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
    leanh::lean_dec(v___y_4339_);
    leanh::lean_dec_ref(v___y_4338_);
    leanh::lean_dec(v___y_4337_);
    leanh::lean_dec_ref(v___y_4336_);
    leanh::lean_dec(v___y_4335_);
    leanh::lean_dec_ref(v___y_4334_);
    leanh::lean_dec(v___y_4333_);
    leanh::lean_dec_ref(v___y_4332_);
    leanh::lean_dec(v___y_4331_);
    leanh::lean_dec(v___y_4330_);
    leanh::lean_dec_ref(v_t_4327_);
    return v_res_4341_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(
    mut v_xs_4342_: *mut leanh::LeanObject,
    mut v_i_4343_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_size_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: u8 = 0;
    v_size_4344_ = leanh::lean_ctor_get(v_xs_4342_, 2);
    v___x_4345_ = lean_nat_dec_lt(v_i_4343_, v_size_4344_);
    return v___x_4345_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0___boxed(
    mut v_xs_4346_: *mut leanh::LeanObject,
    mut v_i_4347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4348_: u8 = 0;
    let mut v_r_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4348_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_xs_4346_, v_i_4347_);
    leanh::lean_dec(v_i_4347_);
    leanh::lean_dec_ref(v_xs_4346_);
    v_r_4349_ = leanh::lean_box((v_res_4348_) as usize);
    return v_r_4349_;
}
pub unsafe fn _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_instInhabitedPersistentArray_default(leanh::lean_box(0));
    return v___x_4350_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(
    mut v_a_4351_: *mut leanh::LeanObject,
    mut v_range_4352_: *mut leanh::LeanObject,
    mut v_b_4353_: *mut leanh::LeanObject,
    mut v_i_4354_: *mut leanh::LeanObject,
    mut v___y_4355_: *mut leanh::LeanObject,
    mut v___y_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
    mut v___y_4365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: u8 = 0;
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: u8 = 0;
    let mut v_dvds_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: u8 = 0;
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: u8 = 0;
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_4367_ = leanh::lean_ctor_get(v_range_4352_, 1);
                v_step_4368_ = leanh::lean_ctor_get(v_range_4352_, 2);
                v___x_4369_ = lean_nat_dec_lt(v_i_4354_, v_stop_4367_);
                if v___x_4369_ == 0 {
                    leanh::lean_dec(v_i_4354_);
                    v___x_4370_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4370_, 0, v_b_4353_);
                    leanh::lean_ctor_set(v___x_4370_, 1, v___y_4355_);
                    v___x_4371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4371_, 0, v___x_4370_);
                    return v___x_4371_;
                } else {
                    v___x_4372_ = l_Lean_Meta_Grind_Arith_Cutsat_eliminated___redArg(
                        v_i_4354_,
                        v___y_4356_,
                        v___y_4364_,
                    );
                    if leanh::lean_obj_tag(v___x_4372_) == 0 {
                        v_a_4373_ = leanh::lean_ctor_get(v___x_4372_, 0);
                        leanh::lean_inc(v_a_4373_);
                        leanh::lean_dec_ref_known(v___x_4372_, 1);
                        v___x_4374_ = leanh::lean_box(0);
                        v___x_4388_ = (leanh::lean_unbox(v_a_4373_) as u8);
                        leanh::lean_dec(v_a_4373_);
                        if v___x_4388_ == 0 {
                            v_dvds_4389_ = leanh::lean_ctor_get(v_a_4351_, 6);
                            v_lowers_4390_ = leanh::lean_ctor_get(v_a_4351_, 7);
                            v_uppers_4391_ = leanh::lean_ctor_get(v_a_4351_, 8);
                            v___x_4403_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0_once), _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___closed__0);
                            v___x_4412_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_lowers_4390_, v_i_4354_);
                            if v___x_4412_ == 0 {
                                v___x_4413_ = l_outOfBounds___redArg(v___x_4403_);
                                v___y_4405_ = v___x_4413_;
                                state = 4;
                                continue;
                            } else {
                                v___x_4414_ = l_Lean_PersistentArray_get_x21___redArg(
                                    v___x_4403_,
                                    v_lowers_4390_,
                                    v_i_4354_,
                                );
                                v___y_4405_ = v___x_4414_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_snd_4376_ = v___y_4355_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___y_4355_);
                        leanh::lean_dec(v_i_4354_);
                        v_a_4415_ = leanh::lean_ctor_get(v___x_4372_, 0);
                        v_isSharedCheck_4422_ =
                            (!leanh::lean_is_exclusive(v___x_4372_)) as u8;
                        if v_isSharedCheck_4422_ == 0 {
                            v___x_4417_ = v___x_4372_;
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4415_);
                            leanh::lean_dec(v___x_4372_);
                            v___x_4417_ = leanh::lean_box(0);
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4377_ = lean_nat_add(v_i_4354_, v_step_4368_);
                leanh::lean_dec(v_i_4354_);
                v_b_4353_ = v___x_4374_;
                v_i_4354_ = v___x_4377_;
                v___y_4355_ = v_snd_4376_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_4381_) == 1 {
                    v_val_4382_ = leanh::lean_ctor_get(v___y_4381_, 0);
                    leanh::lean_inc(v_val_4382_);
                    leanh::lean_dec_ref_known(v___y_4381_, 1);
                    v_d_4383_ = leanh::lean_ctor_get(v_val_4382_, 0);
                    leanh::lean_inc(v_d_4383_);
                    leanh::lean_dec(v_val_4382_);
                    v___x_4384_ = lean_nat_abs(v_d_4383_);
                    leanh::lean_dec(v_d_4383_);
                    v___x_4385_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_updateDvd___redArg(v___x_4384_, v_i_4354_, v___y_4380_);
                    v_a_4386_ = leanh::lean_ctor_get(v___x_4385_, 0);
                    leanh::lean_inc(v_a_4386_);
                    leanh::lean_dec_ref(v___x_4385_);
                    v_snd_4387_ = leanh::lean_ctor_get(v_a_4386_, 1);
                    leanh::lean_inc(v_snd_4387_);
                    leanh::lean_dec(v_a_4386_);
                    v_snd_4376_ = v_snd_4387_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___y_4381_);
                    v_snd_4376_ = v___y_4380_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4395_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_4394_, v___x_4374_, v___y_4393_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
                leanh::lean_dec_ref(v___y_4394_);
                if leanh::lean_obj_tag(v___x_4395_) == 0 {
                    v_a_4396_ = leanh::lean_ctor_get(v___x_4395_, 0);
                    leanh::lean_inc(v_a_4396_);
                    leanh::lean_dec_ref_known(v___x_4395_, 1);
                    v_snd_4397_ = leanh::lean_ctor_get(v_a_4396_, 1);
                    leanh::lean_inc(v_snd_4397_);
                    leanh::lean_dec(v_a_4396_);
                    v_size_4398_ = leanh::lean_ctor_get(v_dvds_4389_, 2);
                    v___x_4399_ = leanh::lean_box(0);
                    v___x_4400_ = lean_nat_dec_lt(v_i_4354_, v_size_4398_);
                    if v___x_4400_ == 0 {
                        v___x_4401_ = l_outOfBounds___redArg(v___x_4399_);
                        v___y_4380_ = v_snd_4397_;
                        v___y_4381_ = v___x_4401_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4402_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_4399_,
                            v_dvds_4389_,
                            v_i_4354_,
                        );
                        v___y_4380_ = v_snd_4397_;
                        v___y_4381_ = v___x_4402_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_i_4354_);
                    return v___x_4395_;
                }
            }
            4 => {
                v___x_4406_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0(v___y_4405_, v___x_4374_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
                leanh::lean_dec_ref(v___y_4405_);
                if leanh::lean_obj_tag(v___x_4406_) == 0 {
                    v_a_4407_ = leanh::lean_ctor_get(v___x_4406_, 0);
                    leanh::lean_inc(v_a_4407_);
                    leanh::lean_dec_ref_known(v___x_4406_, 1);
                    v_snd_4408_ = leanh::lean_ctor_get(v_a_4407_, 1);
                    leanh::lean_inc(v_snd_4408_);
                    leanh::lean_dec(v_a_4407_);
                    v___x_4409_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___lam__0(v_uppers_4391_, v_i_4354_);
                    if v___x_4409_ == 0 {
                        v___x_4410_ = l_outOfBounds___redArg(v___x_4403_);
                        v___y_4393_ = v_snd_4408_;
                        v___y_4394_ = v___x_4410_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4411_ = l_Lean_PersistentArray_get_x21___redArg(
                            v___x_4403_,
                            v_uppers_4391_,
                            v_i_4354_,
                        );
                        v___y_4393_ = v_snd_4408_;
                        v___y_4394_ = v___x_4411_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_i_4354_);
                    return v___x_4406_;
                }
            }
            5 => {
                if v_isShared_4418_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
                    v___x_4420_ = v_reuseFailAlloc_4421_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg___boxed(
    mut v_a_4423_: *mut leanh::LeanObject,
    mut v_range_4424_: *mut leanh::LeanObject,
    mut v_b_4425_: *mut leanh::LeanObject,
    mut v_i_4426_: *mut leanh::LeanObject,
    mut v___y_4427_: *mut leanh::LeanObject,
    mut v___y_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
    mut v___y_4435_: *mut leanh::LeanObject,
    mut v___y_4436_: *mut leanh::LeanObject,
    mut v___y_4437_: *mut leanh::LeanObject,
    mut v___y_4438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_4423_, v_range_4424_, v_b_4425_, v_i_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
    leanh::lean_dec(v___y_4437_);
    leanh::lean_dec_ref(v___y_4436_);
    leanh::lean_dec(v___y_4435_);
    leanh::lean_dec_ref(v___y_4434_);
    leanh::lean_dec(v___y_4433_);
    leanh::lean_dec_ref(v___y_4432_);
    leanh::lean_dec(v___y_4431_);
    leanh::lean_dec_ref(v___y_4430_);
    leanh::lean_dec(v___y_4429_);
    leanh::lean_dec(v___y_4428_);
    leanh::lean_dec_ref(v_range_4424_);
    leanh::lean_dec_ref(v_a_4423_);
    return v_res_4439_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(
    mut v_a_4440_: *mut leanh::LeanObject,
    mut v_a_4441_: *mut leanh::LeanObject,
    mut v_a_4442_: *mut leanh::LeanObject,
    mut v_a_4443_: *mut leanh::LeanObject,
    mut v_a_4444_: *mut leanh::LeanObject,
    mut v_a_4445_: *mut leanh::LeanObject,
    mut v_a_4446_: *mut leanh::LeanObject,
    mut v_a_4447_: *mut leanh::LeanObject,
    mut v_a_4448_: *mut leanh::LeanObject,
    mut v_a_4449_: *mut leanh::LeanObject,
    mut v_a_4450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4464_: u8 = 0;
    let mut v_snd_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4475_: u8 = 0;
    let mut v_unused_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v_a_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4452_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4441_, v_a_4449_);
                if leanh::lean_obj_tag(v___x_4452_) == 0 {
                    v_a_4453_ = leanh::lean_ctor_get(v___x_4452_, 0);
                    leanh::lean_inc(v_a_4453_);
                    leanh::lean_dec_ref_known(v___x_4452_, 1);
                    v_vars_4454_ = leanh::lean_ctor_get(v_a_4453_, 0);
                    v_size_4455_ = leanh::lean_ctor_get(v_vars_4454_, 2);
                    v___x_4456_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4457_ = leanh::lean_unsigned_to_nat(1);
                    leanh::lean_inc(v_size_4455_);
                    v___x_4458_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4458_, 0, v___x_4456_);
                    leanh::lean_ctor_set(v___x_4458_, 1, v_size_4455_);
                    leanh::lean_ctor_set(v___x_4458_, 2, v___x_4457_);
                    v___x_4459_ = leanh::lean_box(0);
                    v___x_4460_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_4453_, v___x_4458_, v___x_4459_, v___x_4456_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_, v_a_4450_);
                    leanh::lean_dec_ref_known(v___x_4458_, 3);
                    leanh::lean_dec(v_a_4453_);
                    if leanh::lean_obj_tag(v___x_4460_) == 0 {
                        v_a_4461_ = leanh::lean_ctor_get(v___x_4460_, 0);
                        v_isSharedCheck_4477_ =
                            (!leanh::lean_is_exclusive(v___x_4460_)) as u8;
                        if v_isSharedCheck_4477_ == 0 {
                            v___x_4463_ = v___x_4460_;
                            v_isShared_4464_ = v_isSharedCheck_4477_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4461_);
                            leanh::lean_dec(v___x_4460_);
                            v___x_4463_ = leanh::lean_box(0);
                            v_isShared_4464_ = v_isSharedCheck_4477_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_4460_;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_4440_);
                    v_a_4478_ = leanh::lean_ctor_get(v___x_4452_, 0);
                    v_isSharedCheck_4485_ = (!leanh::lean_is_exclusive(v___x_4452_)) as u8;
                    if v_isSharedCheck_4485_ == 0 {
                        v___x_4480_ = v___x_4452_;
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4478_);
                        leanh::lean_dec(v___x_4452_);
                        v___x_4480_ = leanh::lean_box(0);
                        v_isShared_4481_ = v_isSharedCheck_4485_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4465_ = leanh::lean_ctor_get(v_a_4461_, 1);
                v_isSharedCheck_4475_ = (!leanh::lean_is_exclusive(v_a_4461_)) as u8;
                if v_isSharedCheck_4475_ == 0 {
                    v_unused_4476_ = leanh::lean_ctor_get(v_a_4461_, 0);
                    leanh::lean_dec(v_unused_4476_);
                    v___x_4467_ = v_a_4461_;
                    v_isShared_4468_ = v_isSharedCheck_4475_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4465_);
                    leanh::lean_dec(v_a_4461_);
                    v___x_4467_ = leanh::lean_box(0);
                    v_isShared_4468_ = v_isSharedCheck_4475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4468_ == 0 {
                    leanh::lean_ctor_set(v___x_4467_, 0, v___x_4459_);
                    v___x_4470_ = v___x_4467_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4474_, 1, v_snd_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4464_ == 0 {
                    leanh::lean_ctor_set(v___x_4463_, 0, v___x_4470_);
                    v___x_4472_ = v___x_4463_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4473_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4470_);
                    v___x_4472_ = v_reuseFailAlloc_4473_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4472_;
            }
            5 => {
                if v_isShared_4481_ == 0 {
                    v___x_4483_ = v___x_4480_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
                    v___x_4483_ = v_reuseFailAlloc_4484_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go___boxed(
    mut v_a_4486_: *mut leanh::LeanObject,
    mut v_a_4487_: *mut leanh::LeanObject,
    mut v_a_4488_: *mut leanh::LeanObject,
    mut v_a_4489_: *mut leanh::LeanObject,
    mut v_a_4490_: *mut leanh::LeanObject,
    mut v_a_4491_: *mut leanh::LeanObject,
    mut v_a_4492_: *mut leanh::LeanObject,
    mut v_a_4493_: *mut leanh::LeanObject,
    mut v_a_4494_: *mut leanh::LeanObject,
    mut v_a_4495_: *mut leanh::LeanObject,
    mut v_a_4496_: *mut leanh::LeanObject,
    mut v_a_4497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4498_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
    leanh::lean_dec(v_a_4496_);
    leanh::lean_dec_ref(v_a_4495_);
    leanh::lean_dec(v_a_4494_);
    leanh::lean_dec_ref(v_a_4493_);
    leanh::lean_dec(v_a_4492_);
    leanh::lean_dec_ref(v_a_4491_);
    leanh::lean_dec(v_a_4490_);
    leanh::lean_dec_ref(v_a_4489_);
    leanh::lean_dec(v_a_4488_);
    leanh::lean_dec(v_a_4487_);
    return v_res_4498_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(
    mut v_a_4499_: *mut leanh::LeanObject,
    mut v_range_4500_: *mut leanh::LeanObject,
    mut v_b_4501_: *mut leanh::LeanObject,
    mut v_i_4502_: *mut leanh::LeanObject,
    mut v_hs_4503_: *mut leanh::LeanObject,
    mut v_hl_4504_: *mut leanh::LeanObject,
    mut v___y_4505_: *mut leanh::LeanObject,
    mut v___y_4506_: *mut leanh::LeanObject,
    mut v___y_4507_: *mut leanh::LeanObject,
    mut v___y_4508_: *mut leanh::LeanObject,
    mut v___y_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
    mut v___y_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4517_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___redArg(v_a_4499_, v_range_4500_, v_b_4501_, v_i_4502_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
    return v___x_4517_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4518_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_range_4519_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_b_4520_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_4521_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_hs_4522_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_hl_4523_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4524_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4525_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4526_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4527_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4528_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4529_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4530_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4531_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4532_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4533_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4534_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4535_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4536_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__1(v_a_4518_, v_range_4519_, v_b_4520_, v_i_4521_, v_hs_4522_, v_hl_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
    leanh::lean_dec(v___y_4534_);
    leanh::lean_dec_ref(v___y_4533_);
    leanh::lean_dec(v___y_4532_);
    leanh::lean_dec_ref(v___y_4531_);
    leanh::lean_dec(v___y_4530_);
    leanh::lean_dec_ref(v___y_4529_);
    leanh::lean_dec(v___y_4528_);
    leanh::lean_dec_ref(v___y_4527_);
    leanh::lean_dec(v___y_4526_);
    leanh::lean_dec(v___y_4525_);
    leanh::lean_dec_ref(v_range_4519_);
    leanh::lean_dec_ref(v_a_4518_);
    return v_res_4536_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(
    mut v_as_4537_: *mut leanh::LeanObject,
    mut v_sz_4538_: usize,
    mut v_i_4539_: usize,
    mut v_b_4540_: *mut leanh::LeanObject,
    mut v___y_4541_: *mut leanh::LeanObject,
    mut v___y_4542_: *mut leanh::LeanObject,
    mut v___y_4543_: *mut leanh::LeanObject,
    mut v___y_4544_: *mut leanh::LeanObject,
    mut v___y_4545_: *mut leanh::LeanObject,
    mut v___y_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
    mut v___y_4549_: *mut leanh::LeanObject,
    mut v___y_4550_: *mut leanh::LeanObject,
    mut v___y_4551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___redArg(v_as_4537_, v_sz_4538_, v_i_4539_, v_b_4540_, v___y_4541_);
    return v___x_4553_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4___boxed(
    mut v_as_4554_: *mut leanh::LeanObject,
    mut v_sz_4555_: *mut leanh::LeanObject,
    mut v_i_4556_: *mut leanh::LeanObject,
    mut v_b_4557_: *mut leanh::LeanObject,
    mut v___y_4558_: *mut leanh::LeanObject,
    mut v___y_4559_: *mut leanh::LeanObject,
    mut v___y_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
    mut v___y_4564_: *mut leanh::LeanObject,
    mut v___y_4565_: *mut leanh::LeanObject,
    mut v___y_4566_: *mut leanh::LeanObject,
    mut v___y_4567_: *mut leanh::LeanObject,
    mut v___y_4568_: *mut leanh::LeanObject,
    mut v___y_4569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4570_: usize = 0;
    let mut v_i_boxed_4571_: usize = 0;
    let mut v_res_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4570_ = leanh::lean_unbox_usize(v_sz_4555_);
    leanh::lean_dec(v_sz_4555_);
    v_i_boxed_4571_ = leanh::lean_unbox_usize(v_i_4556_);
    leanh::lean_dec(v_i_4556_);
    v_res_4572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__1_spec__4(v_as_4554_, v_sz_boxed_4570_, v_i_boxed_4571_, v_b_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
    leanh::lean_dec(v___y_4568_);
    leanh::lean_dec_ref(v___y_4567_);
    leanh::lean_dec(v___y_4566_);
    leanh::lean_dec_ref(v___y_4565_);
    leanh::lean_dec(v___y_4564_);
    leanh::lean_dec_ref(v___y_4563_);
    leanh::lean_dec(v___y_4562_);
    leanh::lean_dec_ref(v___y_4561_);
    leanh::lean_dec(v___y_4560_);
    leanh::lean_dec(v___y_4559_);
    leanh::lean_dec_ref(v_as_4554_);
    return v_res_4572_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(
    mut v_as_4573_: *mut leanh::LeanObject,
    mut v_sz_4574_: usize,
    mut v_i_4575_: usize,
    mut v_b_4576_: *mut leanh::LeanObject,
    mut v___y_4577_: *mut leanh::LeanObject,
    mut v___y_4578_: *mut leanh::LeanObject,
    mut v___y_4579_: *mut leanh::LeanObject,
    mut v___y_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
    mut v___y_4582_: *mut leanh::LeanObject,
    mut v___y_4583_: *mut leanh::LeanObject,
    mut v___y_4584_: *mut leanh::LeanObject,
    mut v___y_4585_: *mut leanh::LeanObject,
    mut v___y_4586_: *mut leanh::LeanObject,
    mut v___y_4587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___redArg(v_as_4573_, v_sz_4574_, v_i_4575_, v_b_4576_, v___y_4577_);
    return v___x_4589_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_as_4590_: *mut leanh::LeanObject,
    mut v_sz_4591_: *mut leanh::LeanObject,
    mut v_i_4592_: *mut leanh::LeanObject,
    mut v_b_4593_: *mut leanh::LeanObject,
    mut v___y_4594_: *mut leanh::LeanObject,
    mut v___y_4595_: *mut leanh::LeanObject,
    mut v___y_4596_: *mut leanh::LeanObject,
    mut v___y_4597_: *mut leanh::LeanObject,
    mut v___y_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
    mut v___y_4601_: *mut leanh::LeanObject,
    mut v___y_4602_: *mut leanh::LeanObject,
    mut v___y_4603_: *mut leanh::LeanObject,
    mut v___y_4604_: *mut leanh::LeanObject,
    mut v___y_4605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4606_: usize = 0;
    let mut v_i_boxed_4607_: usize = 0;
    let mut v_res_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4606_ = leanh::lean_unbox_usize(v_sz_4591_);
    leanh::lean_dec(v_sz_4591_);
    v_i_boxed_4607_ = leanh::lean_unbox_usize(v_i_4592_);
    leanh::lean_dec(v_i_4592_);
    v_res_4608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go_spec__0_spec__0_spec__2_spec__4(v_as_4590_, v_sz_boxed_4606_, v_i_boxed_4607_, v_b_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
    leanh::lean_dec(v___y_4604_);
    leanh::lean_dec_ref(v___y_4603_);
    leanh::lean_dec(v___y_4602_);
    leanh::lean_dec_ref(v___y_4601_);
    leanh::lean_dec(v___y_4600_);
    leanh::lean_dec_ref(v___y_4599_);
    leanh::lean_dec(v___y_4598_);
    leanh::lean_dec_ref(v___y_4597_);
    leanh::lean_dec(v___y_4596_);
    leanh::lean_dec(v___y_4595_);
    leanh::lean_dec_ref(v_as_4590_);
    return v_res_4608_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(
    mut v_a_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
    mut v_a_4611_: *mut leanh::LeanObject,
    mut v_a_4612_: *mut leanh::LeanObject,
    mut v_a_4613_: *mut leanh::LeanObject,
    mut v_a_4614_: *mut leanh::LeanObject,
    mut v_a_4615_: *mut leanh::LeanObject,
    mut v_a_4616_: *mut leanh::LeanObject,
    mut v_a_4617_: *mut leanh::LeanObject,
    mut v_a_4618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4630_: u8 = 0;
    let mut v_snd_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4635_: u8 = 0;
    let mut v_a_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4639_: u8 = 0;
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4643_: u8 = 0;
    let mut v_a_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4647_: u8 = 0;
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4620_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4609_, v_a_4617_);
                if leanh::lean_obj_tag(v___x_4620_) == 0 {
                    v_a_4621_ = leanh::lean_ctor_get(v___x_4620_, 0);
                    leanh::lean_inc(v_a_4621_);
                    leanh::lean_dec_ref_known(v___x_4620_, 1);
                    v_vars_4622_ = leanh::lean_ctor_get(v_a_4621_, 0);
                    leanh::lean_inc_ref(v_vars_4622_);
                    leanh::lean_dec(v_a_4621_);
                    v_size_4623_ = leanh::lean_ctor_get(v_vars_4622_, 2);
                    leanh::lean_inc(v_size_4623_);
                    leanh::lean_dec_ref(v_vars_4622_);
                    v___x_4624_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default___closed__0;
                    v___x_4625_ = lean_mk_array(v_size_4623_, v___x_4624_);
                    v___x_4626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo_go(v___x_4625_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_, v_a_4618_);
                    if leanh::lean_obj_tag(v___x_4626_) == 0 {
                        v_a_4627_ = leanh::lean_ctor_get(v___x_4626_, 0);
                        v_isSharedCheck_4635_ =
                            (!leanh::lean_is_exclusive(v___x_4626_)) as u8;
                        if v_isSharedCheck_4635_ == 0 {
                            v___x_4629_ = v___x_4626_;
                            v_isShared_4630_ = v_isSharedCheck_4635_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4627_);
                            leanh::lean_dec(v___x_4626_);
                            v___x_4629_ = leanh::lean_box(0);
                            v_isShared_4630_ = v_isSharedCheck_4635_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4636_ = leanh::lean_ctor_get(v___x_4626_, 0);
                        v_isSharedCheck_4643_ =
                            (!leanh::lean_is_exclusive(v___x_4626_)) as u8;
                        if v_isSharedCheck_4643_ == 0 {
                            v___x_4638_ = v___x_4626_;
                            v_isShared_4639_ = v_isSharedCheck_4643_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4636_);
                            leanh::lean_dec(v___x_4626_);
                            v___x_4638_ = leanh::lean_box(0);
                            v_isShared_4639_ = v_isSharedCheck_4643_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4644_ = leanh::lean_ctor_get(v___x_4620_, 0);
                    v_isSharedCheck_4651_ = (!leanh::lean_is_exclusive(v___x_4620_)) as u8;
                    if v_isSharedCheck_4651_ == 0 {
                        v___x_4646_ = v___x_4620_;
                        v_isShared_4647_ = v_isSharedCheck_4651_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4644_);
                        leanh::lean_dec(v___x_4620_);
                        v___x_4646_ = leanh::lean_box(0);
                        v_isShared_4647_ = v_isSharedCheck_4651_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4631_ = leanh::lean_ctor_get(v_a_4627_, 1);
                leanh::lean_inc(v_snd_4631_);
                leanh::lean_dec(v_a_4627_);
                if v_isShared_4630_ == 0 {
                    leanh::lean_ctor_set(v___x_4629_, 0, v_snd_4631_);
                    v___x_4633_ = v___x_4629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_snd_4631_);
                    v___x_4633_ = v_reuseFailAlloc_4634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4633_;
            }
            3 => {
                if v_isShared_4639_ == 0 {
                    v___x_4641_ = v___x_4638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4642_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
                    v___x_4641_ = v_reuseFailAlloc_4642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4641_;
            }
            5 => {
                if v_isShared_4647_ == 0 {
                    v___x_4649_ = v___x_4646_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4650_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
                    v___x_4649_ = v_reuseFailAlloc_4650_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo___boxed(
    mut v_a_4652_: *mut leanh::LeanObject,
    mut v_a_4653_: *mut leanh::LeanObject,
    mut v_a_4654_: *mut leanh::LeanObject,
    mut v_a_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
    mut v_a_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
    mut v_a_4661_: *mut leanh::LeanObject,
    mut v_a_4662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4663_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_);
    leanh::lean_dec(v_a_4661_);
    leanh::lean_dec_ref(v_a_4660_);
    leanh::lean_dec(v_a_4659_);
    leanh::lean_dec_ref(v_a_4658_);
    leanh::lean_dec(v_a_4657_);
    leanh::lean_dec_ref(v_a_4656_);
    leanh::lean_dec(v_a_4655_);
    leanh::lean_dec_ref(v_a_4654_);
    leanh::lean_dec(v_a_4653_);
    leanh::lean_dec(v_a_4652_);
    return v_res_4663_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(
    mut v_info_4664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_maxLowerCoeff_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxUpperCoeff_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDvdCoeff_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxLowerCoeff_4665_ = leanh::lean_ctor_get(v_info_4664_, 0);
                v_maxUpperCoeff_4666_ = leanh::lean_ctor_get(v_info_4664_, 1);
                v_maxDvdCoeff_4667_ = leanh::lean_ctor_get(v_info_4664_, 2);
                v___x_4671_ = lean_nat_dec_le(v_maxLowerCoeff_4665_, v_maxUpperCoeff_4666_);
                if v___x_4671_ == 0 {
                    v___y_4669_ = v_maxUpperCoeff_4666_;
                    state = 1;
                    continue;
                } else {
                    v___y_4669_ = v_maxLowerCoeff_4665_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4670_ = lean_nat_dec_le(v_maxDvdCoeff_4667_, v___y_4669_);
                if v___x_4670_ == 0 {
                    leanh::lean_inc(v_maxDvdCoeff_4667_);
                    return v_maxDvdCoeff_4667_;
                } else {
                    leanh::lean_inc(v___y_4669_);
                    return v___y_4669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081___boxed(
    mut v_info_4672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4673_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v_info_4672_);
    leanh::lean_dec_ref(v_info_4672_);
    return v_res_4673_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(
    mut v_infos_4674_: *mut leanh::LeanObject,
    mut v_x_4675_: *mut leanh::LeanObject,
    mut v_y_4676_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    v___x_4677_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default;
    v___x_4678_ = lean_array_get_borrowed(v___x_4677_, v_infos_4674_, v_x_4675_);
    v___x_4679_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_4678_);
    v___x_4680_ = lean_array_get_borrowed(v___x_4677_, v_infos_4674_, v_y_4676_);
    v___x_4681_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2081(v___x_4680_);
    v___x_4682_ = lean_nat_dec_lt(v___x_4679_, v___x_4681_);
    if v___x_4682_ == 0 {
        let mut v___x_4683_: u8 = 0;
        v___x_4683_ = lean_nat_dec_eq(v___x_4679_, v___x_4681_);
        leanh::lean_dec(v___x_4681_);
        leanh::lean_dec(v___x_4679_);
        if v___x_4683_ == 0 {
            let mut v___x_4684_: u8 = 0;
            v___x_4684_ = 0;
            return v___x_4684_;
        } else {
            let mut v___x_4685_: u8 = 0;
            v___x_4685_ = 1;
            return v___x_4685_;
        }
    } else {
        let mut v___x_4686_: u8 = 0;
        leanh::lean_dec(v___x_4681_);
        leanh::lean_dec(v___x_4679_);
        v___x_4686_ = 2;
        return v___x_4686_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081___boxed(
    mut v_infos_4687_: *mut leanh::LeanObject,
    mut v_x_4688_: *mut leanh::LeanObject,
    mut v_y_4689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4690_: u8 = 0;
    let mut v_r_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_4687_, v_x_4688_, v_y_4689_);
    leanh::lean_dec(v_y_4689_);
    leanh::lean_dec(v_x_4688_);
    leanh::lean_dec_ref(v_infos_4687_);
    v_r_4691_ = leanh::lean_box((v_res_4690_) as usize);
    return v_r_4691_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(
    mut v_info_4692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_maxLowerCoeff_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxUpperCoeff_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxDvdCoeff_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: u8 = 0;
    let mut v___x_4699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_maxLowerCoeff_4693_ = leanh::lean_ctor_get(v_info_4692_, 0);
                v_maxUpperCoeff_4694_ = leanh::lean_ctor_get(v_info_4692_, 1);
                v_maxDvdCoeff_4695_ = leanh::lean_ctor_get(v_info_4692_, 2);
                v___x_4699_ = lean_nat_dec_le(v_maxLowerCoeff_4693_, v_maxUpperCoeff_4694_);
                if v___x_4699_ == 0 {
                    v___y_4697_ = v_maxLowerCoeff_4693_;
                    state = 1;
                    continue;
                } else {
                    v___y_4697_ = v_maxUpperCoeff_4694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4698_ = lean_nat_dec_le(v_maxDvdCoeff_4695_, v___y_4697_);
                if v___x_4698_ == 0 {
                    leanh::lean_inc(v_maxDvdCoeff_4695_);
                    return v_maxDvdCoeff_4695_;
                } else {
                    leanh::lean_inc(v___y_4697_);
                    return v___y_4697_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082___boxed(
    mut v_info_4700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4701_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v_info_4700_);
    leanh::lean_dec_ref(v_info_4700_);
    return v_res_4701_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(
    mut v_infos_4702_: *mut leanh::LeanObject,
    mut v_x_4703_: *mut leanh::LeanObject,
    mut v_y_4704_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: u8 = 0;
    v___x_4705_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedVarInfo_default;
    v___x_4706_ = lean_array_get_borrowed(v___x_4705_, v_infos_4702_, v_x_4703_);
    v___x_4707_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_4706_);
    v___x_4708_ = lean_array_get_borrowed(v___x_4705_, v_infos_4702_, v_y_4704_);
    v___x_4709_ = l_Lean_Meta_Grind_Arith_Cutsat_cost_u2082(v___x_4708_);
    v___x_4710_ = lean_nat_dec_lt(v___x_4707_, v___x_4709_);
    if v___x_4710_ == 0 {
        let mut v___x_4711_: u8 = 0;
        v___x_4711_ = lean_nat_dec_eq(v___x_4707_, v___x_4709_);
        leanh::lean_dec(v___x_4709_);
        leanh::lean_dec(v___x_4707_);
        if v___x_4711_ == 0 {
            let mut v___x_4712_: u8 = 0;
            v___x_4712_ = 0;
            return v___x_4712_;
        } else {
            let mut v___x_4713_: u8 = 0;
            v___x_4713_ = 1;
            return v___x_4713_;
        }
    } else {
        let mut v___x_4714_: u8 = 0;
        leanh::lean_dec(v___x_4709_);
        leanh::lean_dec(v___x_4707_);
        v___x_4714_ = 2;
        return v___x_4714_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082___boxed(
    mut v_infos_4715_: *mut leanh::LeanObject,
    mut v_x_4716_: *mut leanh::LeanObject,
    mut v_y_4717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4718_: u8 = 0;
    let mut v_r_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4718_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_4715_, v_x_4716_, v_y_4717_);
    leanh::lean_dec(v_y_4717_);
    leanh::lean_dec(v_x_4716_);
    leanh::lean_dec_ref(v_infos_4715_);
    v_r_4719_ = leanh::lean_box((v_res_4718_) as usize);
    return v_r_4719_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(
    mut v_infos_4720_: *mut leanh::LeanObject,
    mut v_x_4721_: *mut leanh::LeanObject,
    mut v_y_4722_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4724_: u8 = 0;
    let mut v___x_4725_: u8 = 0;
    let mut v___x_4726_: u8 = 0;
    let mut v___x_4727_: u8 = 0;
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4729_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2081(v_infos_4720_, v_x_4721_, v_y_4722_);
                if v___x_4729_ == 1 {
                    v___x_4730_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp_u2082(v_infos_4720_, v_x_4721_, v_y_4722_);
                    v___y_4724_ = v___x_4730_;
                    state = 1;
                    continue;
                } else {
                    v___y_4724_ = v___x_4729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4724_ == 1 {
                    v___x_4725_ = lean_nat_dec_lt(v_x_4721_, v_y_4722_);
                    if v___x_4725_ == 0 {
                        v___x_4726_ = lean_nat_dec_eq(v_x_4721_, v_y_4722_);
                        if v___x_4726_ == 0 {
                            v___x_4727_ = 2;
                            return v___x_4727_;
                        } else {
                            return v___y_4724_;
                        }
                    } else {
                        v___x_4728_ = 0;
                        return v___x_4728_;
                    }
                } else {
                    return v___y_4724_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp___boxed(
    mut v_infos_4731_: *mut leanh::LeanObject,
    mut v_x_4732_: *mut leanh::LeanObject,
    mut v_y_4733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4734_: u8 = 0;
    let mut v_r_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4734_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_infos_4731_, v_x_4732_, v_y_4733_);
    leanh::lean_dec(v_y_4733_);
    leanh::lean_dec(v_x_4732_);
    leanh::lean_dec_ref(v_infos_4731_);
    v_r_4735_ = leanh::lean_box((v_res_4734_) as usize);
    return v_r_4735_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(
    mut v_a_4736_: *mut leanh::LeanObject,
    mut v_x_4737_: *mut leanh::LeanObject,
    mut v_y_4738_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4739_: u8 = 0;
    let mut v___x_4740_: u8 = 0;
    let mut v___x_4741_: u8 = 0;
    v___x_4739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_a_4736_, v_x_4737_, v_y_4738_);
    v___x_4740_ = 0;
    v___x_4741_ = l_instDecidableEqOrdering(v___x_4739_, v___x_4740_);
    return v___x_4741_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0___boxed(
    mut v_a_4742_: *mut leanh::LeanObject,
    mut v_x_4743_: *mut leanh::LeanObject,
    mut v_y_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4745_: u8 = 0;
    let mut v_r_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_4742_, v_x_4743_, v_y_4744_);
    leanh::lean_dec(v_y_4744_);
    leanh::lean_dec(v_x_4743_);
    leanh::lean_dec_ref(v_a_4742_);
    v_r_4746_ = leanh::lean_box((v_res_4745_) as usize);
    return v_r_4746_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(
    mut v_a_4747_: *mut leanh::LeanObject,
    mut v_hi_4748_: *mut leanh::LeanObject,
    mut v_pivot_4749_: *mut leanh::LeanObject,
    mut v_as_4750_: *mut leanh::LeanObject,
    mut v_i_4751_: *mut leanh::LeanObject,
    mut v_k_4752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4753_: u8 = 0;
    let mut v___x_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: u8 = 0;
    let mut v___x_4758_: u8 = 0;
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4753_ = lean_nat_dec_lt(v_k_4752_, v_hi_4748_);
                if v___x_4753_ == 0 {
                    leanh::lean_dec(v_k_4752_);
                    v___x_4754_ = lean_array_fswap(v_as_4750_, v_i_4751_, v_hi_4748_);
                    v___x_4755_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4755_, 0, v_i_4751_);
                    leanh::lean_ctor_set(v___x_4755_, 1, v___x_4754_);
                    return v___x_4755_;
                } else {
                    v___x_4756_ = lean_array_fget_borrowed(v_as_4750_, v_k_4752_);
                    v___x_4757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_cmp(v_a_4747_, v___x_4756_, v_pivot_4749_);
                    v___x_4758_ = 0;
                    v___x_4759_ = l_instDecidableEqOrdering(v___x_4757_, v___x_4758_);
                    if v___x_4759_ == 0 {
                        v___x_4760_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4761_ = lean_nat_add(v_k_4752_, v___x_4760_);
                        leanh::lean_dec(v_k_4752_);
                        v_k_4752_ = v___x_4761_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4763_ = lean_array_fswap(v_as_4750_, v_i_4751_, v_k_4752_);
                        v___x_4764_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4765_ = lean_nat_add(v_i_4751_, v___x_4764_);
                        leanh::lean_dec(v_i_4751_);
                        v___x_4766_ = lean_nat_add(v_k_4752_, v___x_4764_);
                        leanh::lean_dec(v_k_4752_);
                        v_as_4750_ = v___x_4763_;
                        v_i_4751_ = v___x_4765_;
                        v_k_4752_ = v___x_4766_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg___boxed(
    mut v_a_4768_: *mut leanh::LeanObject,
    mut v_hi_4769_: *mut leanh::LeanObject,
    mut v_pivot_4770_: *mut leanh::LeanObject,
    mut v_as_4771_: *mut leanh::LeanObject,
    mut v_i_4772_: *mut leanh::LeanObject,
    mut v_k_4773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4774_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_4768_, v_hi_4769_, v_pivot_4770_, v_as_4771_, v_i_4772_, v_k_4773_);
    leanh::lean_dec(v_pivot_4770_);
    leanh::lean_dec(v_hi_4769_);
    leanh::lean_dec_ref(v_a_4768_);
    return v_res_4774_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(
    mut v_a_4775_: *mut leanh::LeanObject,
    mut v_n_4776_: *mut leanh::LeanObject,
    mut v_as_4777_: *mut leanh::LeanObject,
    mut v_lo_4778_: *mut leanh::LeanObject,
    mut v_hi_4779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: u8 = 0;
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: u8 = 0;
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: u8 = 0;
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: u8 = 0;
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4791_ = lean_nat_dec_lt(v_lo_4778_, v_hi_4779_);
                if v___x_4791_ == 0 {
                    leanh::lean_dec(v_lo_4778_);
                    return v_as_4777_;
                } else {
                    v___x_4792_ = lean_nat_add(v_lo_4778_, v_hi_4779_);
                    v___x_4793_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_4794_ = lean_nat_shiftr(v___x_4792_, v___x_4793_);
                    leanh::lean_dec(v___x_4792_);
                    v___x_4807_ = lean_array_fget_borrowed(v_as_4777_, v_mid_4794_);
                    v___x_4808_ = lean_array_fget_borrowed(v_as_4777_, v_lo_4778_);
                    v___x_4809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_4775_, v___x_4807_, v___x_4808_);
                    if v___x_4809_ == 0 {
                        v___y_4802_ = v_as_4777_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4810_ = lean_array_fswap(v_as_4777_, v_lo_4778_, v_mid_4794_);
                        v___y_4802_ = v___x_4810_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_4782_ = lean_array_fget(v___y_4781_, v_hi_4779_);
                leanh::lean_inc_n(v_lo_4778_, 2);
                v___x_4783_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_4775_, v_hi_4779_, v_pivot_4782_, v___y_4781_, v_lo_4778_, v_lo_4778_);
                leanh::lean_dec(v_pivot_4782_);
                v_fst_4784_ = leanh::lean_ctor_get(v___x_4783_, 0);
                leanh::lean_inc(v_fst_4784_);
                v_snd_4785_ = leanh::lean_ctor_get(v___x_4783_, 1);
                leanh::lean_inc(v_snd_4785_);
                leanh::lean_dec_ref(v___x_4783_);
                v___x_4786_ = lean_nat_dec_le(v_hi_4779_, v_fst_4784_);
                if v___x_4786_ == 0 {
                    v___x_4787_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_4775_, v_n_4776_, v_snd_4785_, v_lo_4778_, v_fst_4784_);
                    v___x_4788_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4789_ = lean_nat_add(v_fst_4784_, v___x_4788_);
                    leanh::lean_dec(v_fst_4784_);
                    v_as_4777_ = v___x_4787_;
                    v_lo_4778_ = v___x_4789_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_4784_);
                    leanh::lean_dec(v_lo_4778_);
                    return v_snd_4785_;
                }
            }
            2 => {
                v___x_4797_ = lean_array_fget_borrowed(v___y_4796_, v_mid_4794_);
                v___x_4798_ = lean_array_fget_borrowed(v___y_4796_, v_hi_4779_);
                v___x_4799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_4775_, v___x_4797_, v___x_4798_);
                if v___x_4799_ == 0 {
                    leanh::lean_dec(v_mid_4794_);
                    v___y_4781_ = v___y_4796_;
                    state = 1;
                    continue;
                } else {
                    v___x_4800_ = lean_array_fswap(v___y_4796_, v_mid_4794_, v_hi_4779_);
                    leanh::lean_dec(v_mid_4794_);
                    v___y_4781_ = v___x_4800_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4803_ = lean_array_fget_borrowed(v___y_4802_, v_hi_4779_);
                v___x_4804_ = lean_array_fget_borrowed(v___y_4802_, v_lo_4778_);
                v___x_4805_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___lam__0(v_a_4775_, v___x_4803_, v___x_4804_);
                if v___x_4805_ == 0 {
                    v___y_4796_ = v___y_4802_;
                    state = 2;
                    continue;
                } else {
                    v___x_4806_ = lean_array_fswap(v___y_4802_, v_lo_4778_, v_hi_4779_);
                    v___y_4796_ = v___x_4806_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg___boxed(
    mut v_a_4811_: *mut leanh::LeanObject,
    mut v_n_4812_: *mut leanh::LeanObject,
    mut v_as_4813_: *mut leanh::LeanObject,
    mut v_lo_4814_: *mut leanh::LeanObject,
    mut v_hi_4815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_4811_, v_n_4812_, v_as_4813_, v_lo_4814_, v_hi_4815_);
    leanh::lean_dec(v_hi_4815_);
    leanh::lean_dec(v_n_4812_);
    leanh::lean_dec_ref(v_a_4811_);
    return v_res_4816_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(
    mut v_a_4817_: *mut leanh::LeanObject,
    mut v_a_4818_: *mut leanh::LeanObject,
    mut v_a_4819_: *mut leanh::LeanObject,
    mut v_a_4820_: *mut leanh::LeanObject,
    mut v_a_4821_: *mut leanh::LeanObject,
    mut v_a_4822_: *mut leanh::LeanObject,
    mut v_a_4823_: *mut leanh::LeanObject,
    mut v_a_4824_: *mut leanh::LeanObject,
    mut v_a_4825_: *mut leanh::LeanObject,
    mut v_a_4826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4832_: u8 = 0;
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v_vars_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: u8 = 0;
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: u8 = 0;
    let mut v___x_4856_: u8 = 0;
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_a_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4864_: u8 = 0;
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4868_: u8 = 0;
    let mut v_isSharedCheck_4869_: u8 = 0;
    let mut v_a_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4873_: u8 = 0;
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4828_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_collectVarInfo(v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_, v_a_4826_);
                if leanh::lean_obj_tag(v___x_4828_) == 0 {
                    v_a_4829_ = leanh::lean_ctor_get(v___x_4828_, 0);
                    v_isSharedCheck_4869_ = (!leanh::lean_is_exclusive(v___x_4828_)) as u8;
                    if v_isSharedCheck_4869_ == 0 {
                        v___x_4831_ = v___x_4828_;
                        v_isShared_4832_ = v_isSharedCheck_4869_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4829_);
                        leanh::lean_dec(v___x_4828_);
                        v___x_4831_ = leanh::lean_box(0);
                        v_isShared_4832_ = v_isSharedCheck_4869_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4870_ = leanh::lean_ctor_get(v___x_4828_, 0);
                    v_isSharedCheck_4877_ = (!leanh::lean_is_exclusive(v___x_4828_)) as u8;
                    if v_isSharedCheck_4877_ == 0 {
                        v___x_4872_ = v___x_4828_;
                        v_isShared_4873_ = v_isSharedCheck_4877_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4870_);
                        leanh::lean_dec(v___x_4828_);
                        v___x_4872_ = leanh::lean_box(0);
                        v_isShared_4873_ = v_isSharedCheck_4877_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4833_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_4817_, v_a_4825_);
                if leanh::lean_obj_tag(v___x_4833_) == 0 {
                    v_a_4834_ = leanh::lean_ctor_get(v___x_4833_, 0);
                    v_isSharedCheck_4860_ = (!leanh::lean_is_exclusive(v___x_4833_)) as u8;
                    if v_isSharedCheck_4860_ == 0 {
                        v___x_4836_ = v___x_4833_;
                        v_isShared_4837_ = v_isSharedCheck_4860_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4834_);
                        leanh::lean_dec(v___x_4833_);
                        v___x_4836_ = leanh::lean_box(0);
                        v_isShared_4837_ = v_isSharedCheck_4860_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4831_);
                    leanh::lean_dec(v_a_4829_);
                    v_a_4861_ = leanh::lean_ctor_get(v___x_4833_, 0);
                    v_isSharedCheck_4868_ = (!leanh::lean_is_exclusive(v___x_4833_)) as u8;
                    if v_isSharedCheck_4868_ == 0 {
                        v___x_4863_ = v___x_4833_;
                        v_isShared_4864_ = v_isSharedCheck_4868_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4861_);
                        leanh::lean_dec(v___x_4833_);
                        v___x_4863_ = leanh::lean_box(0);
                        v_isShared_4864_ = v_isSharedCheck_4868_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_vars_4838_ = leanh::lean_ctor_get(v_a_4834_, 0);
                leanh::lean_inc_ref(v_vars_4838_);
                leanh::lean_dec(v_a_4834_);
                v_size_4839_ = leanh::lean_ctor_get(v_vars_4838_, 2);
                leanh::lean_inc(v_size_4839_);
                leanh::lean_dec_ref(v_vars_4838_);
                v___x_4840_ = l_Array_range(v_size_4839_);
                v___x_4841_ = lean_array_get_size(v___x_4840_);
                v___x_4849_ = leanh::lean_unsigned_to_nat(0);
                v___x_4850_ = lean_nat_dec_eq(v___x_4841_, v___x_4849_);
                if v___x_4850_ == 0 {
                    leanh::lean_del_object(v___x_4831_);
                    v___x_4851_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4852_ = lean_nat_sub(v___x_4841_, v___x_4851_);
                    v___x_4856_ = lean_nat_dec_le(v___x_4849_, v___x_4852_);
                    if v___x_4856_ == 0 {
                        leanh::lean_inc(v___x_4852_);
                        v___y_4854_ = v___x_4852_;
                        state = 5;
                        continue;
                    } else {
                        v___y_4854_ = v___x_4849_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4836_);
                    leanh::lean_dec(v_a_4829_);
                    if v_isShared_4832_ == 0 {
                        leanh::lean_ctor_set(v___x_4831_, 0, v___x_4840_);
                        v___x_4858_ = v___x_4831_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4859_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4840_);
                        v___x_4858_ = v_reuseFailAlloc_4859_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_4829_, v___x_4841_, v___x_4840_, v___y_4843_, v___y_4844_);
                leanh::lean_dec(v___y_4844_);
                leanh::lean_dec(v_a_4829_);
                if v_isShared_4837_ == 0 {
                    leanh::lean_ctor_set(v___x_4836_, 0, v___x_4845_);
                    v___x_4847_ = v___x_4836_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v___x_4845_);
                    v___x_4847_ = v_reuseFailAlloc_4848_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4847_;
            }
            5 => {
                v___x_4855_ = lean_nat_dec_le(v___y_4854_, v___x_4852_);
                if v___x_4855_ == 0 {
                    leanh::lean_dec(v___x_4852_);
                    leanh::lean_inc(v___y_4854_);
                    v___y_4843_ = v___y_4854_;
                    v___y_4844_ = v___y_4854_;
                    state = 3;
                    continue;
                } else {
                    v___y_4843_ = v___y_4854_;
                    v___y_4844_ = v___x_4852_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                return v___x_4858_;
            }
            7 => {
                if v_isShared_4864_ == 0 {
                    v___x_4866_ = v___x_4863_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4867_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4867_, 0, v_a_4861_);
                    v___x_4866_ = v_reuseFailAlloc_4867_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4866_;
            }
            9 => {
                if v_isShared_4873_ == 0 {
                    v___x_4875_ = v___x_4872_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4876_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_a_4870_);
                    v___x_4875_ = v_reuseFailAlloc_4876_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars___boxed(
    mut v_a_4878_: *mut leanh::LeanObject,
    mut v_a_4879_: *mut leanh::LeanObject,
    mut v_a_4880_: *mut leanh::LeanObject,
    mut v_a_4881_: *mut leanh::LeanObject,
    mut v_a_4882_: *mut leanh::LeanObject,
    mut v_a_4883_: *mut leanh::LeanObject,
    mut v_a_4884_: *mut leanh::LeanObject,
    mut v_a_4885_: *mut leanh::LeanObject,
    mut v_a_4886_: *mut leanh::LeanObject,
    mut v_a_4887_: *mut leanh::LeanObject,
    mut v_a_4888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4889_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_, v_a_4887_);
    leanh::lean_dec(v_a_4887_);
    leanh::lean_dec_ref(v_a_4886_);
    leanh::lean_dec(v_a_4885_);
    leanh::lean_dec_ref(v_a_4884_);
    leanh::lean_dec(v_a_4883_);
    leanh::lean_dec_ref(v_a_4882_);
    leanh::lean_dec(v_a_4881_);
    leanh::lean_dec_ref(v_a_4880_);
    leanh::lean_dec(v_a_4879_);
    leanh::lean_dec(v_a_4878_);
    return v_res_4889_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(
    mut v_a_4890_: *mut leanh::LeanObject,
    mut v_n_4891_: *mut leanh::LeanObject,
    mut v_as_4892_: *mut leanh::LeanObject,
    mut v_lo_4893_: *mut leanh::LeanObject,
    mut v_hi_4894_: *mut leanh::LeanObject,
    mut v_w_4895_: *mut leanh::LeanObject,
    mut v_hlo_4896_: *mut leanh::LeanObject,
    mut v_hhi_4897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___redArg(v_a_4890_, v_n_4891_, v_as_4892_, v_lo_4893_, v_hi_4894_);
    return v___x_4898_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0___boxed(
    mut v_a_4899_: *mut leanh::LeanObject,
    mut v_n_4900_: *mut leanh::LeanObject,
    mut v_as_4901_: *mut leanh::LeanObject,
    mut v_lo_4902_: *mut leanh::LeanObject,
    mut v_hi_4903_: *mut leanh::LeanObject,
    mut v_w_4904_: *mut leanh::LeanObject,
    mut v_hlo_4905_: *mut leanh::LeanObject,
    mut v_hhi_4906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4907_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0(v_a_4899_, v_n_4900_, v_as_4901_, v_lo_4902_, v_hi_4903_, v_w_4904_, v_hlo_4905_, v_hhi_4906_);
    leanh::lean_dec(v_hi_4903_);
    leanh::lean_dec(v_n_4900_);
    leanh::lean_dec_ref(v_a_4899_);
    return v_res_4907_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(
    mut v_a_4908_: *mut leanh::LeanObject,
    mut v_n_4909_: *mut leanh::LeanObject,
    mut v_lo_4910_: *mut leanh::LeanObject,
    mut v_hi_4911_: *mut leanh::LeanObject,
    mut v_hhi_4912_: *mut leanh::LeanObject,
    mut v_pivot_4913_: *mut leanh::LeanObject,
    mut v_as_4914_: *mut leanh::LeanObject,
    mut v_i_4915_: *mut leanh::LeanObject,
    mut v_k_4916_: *mut leanh::LeanObject,
    mut v_ilo_4917_: *mut leanh::LeanObject,
    mut v_ik_4918_: *mut leanh::LeanObject,
    mut v_w_4919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___redArg(v_a_4908_, v_hi_4911_, v_pivot_4913_, v_as_4914_, v_i_4915_, v_k_4916_);
    return v___x_4920_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0___boxed(
    mut v_a_4921_: *mut leanh::LeanObject,
    mut v_n_4922_: *mut leanh::LeanObject,
    mut v_lo_4923_: *mut leanh::LeanObject,
    mut v_hi_4924_: *mut leanh::LeanObject,
    mut v_hhi_4925_: *mut leanh::LeanObject,
    mut v_pivot_4926_: *mut leanh::LeanObject,
    mut v_as_4927_: *mut leanh::LeanObject,
    mut v_i_4928_: *mut leanh::LeanObject,
    mut v_k_4929_: *mut leanh::LeanObject,
    mut v_ilo_4930_: *mut leanh::LeanObject,
    mut v_ik_4931_: *mut leanh::LeanObject,
    mut v_w_4932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4933_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars_spec__0_spec__0(v_a_4921_, v_n_4922_, v_lo_4923_, v_hi_4924_, v_hhi_4925_, v_pivot_4926_, v_as_4927_, v_i_4928_, v_k_4929_, v_ilo_4930_, v_ik_4931_, v_w_4932_);
    leanh::lean_dec(v_pivot_4926_);
    leanh::lean_dec(v_hi_4924_);
    leanh::lean_dec(v_lo_4923_);
    leanh::lean_dec(v_n_4922_);
    leanh::lean_dec_ref(v_a_4921_);
    return v_res_4933_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(
    mut v_perm_4934_: *mut leanh::LeanObject,
    mut v_range_4935_: *mut leanh::LeanObject,
    mut v_b_4936_: *mut leanh::LeanObject,
    mut v_i_4937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: u8 = 0;
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inv_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_4938_ = leanh::lean_ctor_get(v_range_4935_, 1);
                v_step_4939_ = leanh::lean_ctor_get(v_range_4935_, 2);
                v___x_4940_ = lean_nat_dec_lt(v_i_4937_, v_stop_4938_);
                if v___x_4940_ == 0 {
                    leanh::lean_dec(v_i_4937_);
                    return v_b_4936_;
                } else {
                    v___x_4941_ = lean_array_fget_borrowed(v_perm_4934_, v_i_4937_);
                    leanh::lean_inc(v_i_4937_);
                    v_inv_4942_ = lean_array_set(v_b_4936_, v___x_4941_, v_i_4937_);
                    v___x_4943_ = lean_nat_add(v_i_4937_, v_step_4939_);
                    leanh::lean_dec(v_i_4937_);
                    v_b_4936_ = v_inv_4942_;
                    v_i_4937_ = v___x_4943_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg___boxed(
    mut v_perm_4945_: *mut leanh::LeanObject,
    mut v_range_4946_: *mut leanh::LeanObject,
    mut v_b_4947_: *mut leanh::LeanObject,
    mut v_i_4948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4949_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_4945_, v_range_4946_, v_b_4947_, v_i_4948_);
    leanh::lean_dec_ref(v_range_4946_);
    leanh::lean_dec_ref(v_perm_4945_);
    return v_res_4949_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(
    mut v_perm_4950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inv_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4951_ = lean_array_get_size(v_perm_4950_);
    v___x_4952_ = leanh::lean_unsigned_to_nat(0);
    v_inv_4953_ = lean_mk_array(v___x_4951_, v___x_4952_);
    v___x_4954_ = leanh::lean_unsigned_to_nat(1);
    v___x_4955_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4955_, 0, v___x_4952_);
    leanh::lean_ctor_set(v___x_4955_, 1, v___x_4951_);
    leanh::lean_ctor_set(v___x_4955_, 2, v___x_4954_);
    v___x_4956_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_4950_, v___x_4955_, v_inv_4953_, v___x_4952_);
    leanh::lean_dec_ref_known(v___x_4955_, 3);
    return v___x_4956_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv___boxed(
    mut v_perm_4957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_perm_4957_);
    leanh::lean_dec_ref(v_perm_4957_);
    return v_res_4958_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(
    mut v_perm_4959_: *mut leanh::LeanObject,
    mut v_range_4960_: *mut leanh::LeanObject,
    mut v_b_4961_: *mut leanh::LeanObject,
    mut v_i_4962_: *mut leanh::LeanObject,
    mut v_hs_4963_: *mut leanh::LeanObject,
    mut v_hl_4964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4965_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___redArg(v_perm_4959_, v_range_4960_, v_b_4961_, v_i_4962_);
    return v___x_4965_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0___boxed(
    mut v_perm_4966_: *mut leanh::LeanObject,
    mut v_range_4967_: *mut leanh::LeanObject,
    mut v_b_4968_: *mut leanh::LeanObject,
    mut v_i_4969_: *mut leanh::LeanObject,
    mut v_hs_4970_: *mut leanh::LeanObject,
    mut v_hl_4971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4972_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv_spec__0(v_perm_4966_, v_range_4967_, v_b_4968_, v_i_4969_, v_hs_4970_, v_hl_4971_);
    leanh::lean_dec_ref(v_range_4967_);
    leanh::lean_dec_ref(v_perm_4966_);
    return v_res_4972_;
}
pub unsafe fn l_Int_Linear_Poly_reorder(
    mut v_p_4973_: *mut leanh::LeanObject,
    mut v_old2new_4974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4980_: u8 = 0;
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_4973_) == 0 {
                    return v_p_4973_;
                } else {
                    v_k_4975_ = leanh::lean_ctor_get(v_p_4973_, 0);
                    v_v_4976_ = leanh::lean_ctor_get(v_p_4973_, 1);
                    v_p_4977_ = leanh::lean_ctor_get(v_p_4973_, 2);
                    v_isSharedCheck_4987_ = (!leanh::lean_is_exclusive(v_p_4973_)) as u8;
                    if v_isSharedCheck_4987_ == 0 {
                        v___x_4979_ = v_p_4973_;
                        v_isShared_4980_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_p_4977_);
                        leanh::lean_inc(v_v_4976_);
                        leanh::lean_inc(v_k_4975_);
                        leanh::lean_dec(v_p_4973_);
                        v___x_4979_ = leanh::lean_box(0);
                        v_isShared_4980_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4981_ = leanh::lean_unsigned_to_nat(0);
                v___x_4982_ = lean_array_get_borrowed(v___x_4981_, v_old2new_4974_, v_v_4976_);
                leanh::lean_dec(v_v_4976_);
                v___x_4983_ = l_Int_Linear_Poly_reorder(v_p_4977_, v_old2new_4974_);
                leanh::lean_inc(v___x_4982_);
                if v_isShared_4980_ == 0 {
                    leanh::lean_ctor_set(v___x_4979_, 2, v___x_4983_);
                    leanh::lean_ctor_set(v___x_4979_, 1, v___x_4982_);
                    v___x_4985_ = v___x_4979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4986_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_k_4975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4986_, 1, v___x_4982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4986_, 2, v___x_4983_);
                    v___x_4985_ = v_reuseFailAlloc_4986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_Linear_Poly_reorder___boxed(
    mut v_p_4988_: *mut leanh::LeanObject,
    mut v_old2new_4989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4990_ = l_Int_Linear_Poly_reorder(v_p_4988_, v_old2new_4989_);
    leanh::lean_dec_ref(v_old2new_4989_);
    return v_res_4990_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(
    mut v_c_4991_: *mut leanh::LeanObject,
    mut v_old2new_4992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_d_4993_ = leanh::lean_ctor_get(v_c_4991_, 0);
    leanh::lean_inc(v_d_4993_);
    v_p_4994_ = leanh::lean_ctor_get(v_c_4991_, 1);
    leanh::lean_inc_ref(v_p_4994_);
    v___x_4995_ = l_Int_Linear_Poly_reorder(v_p_4994_, v_old2new_4992_);
    v___x_4996_ = leanh::lean_alloc_ctor(11, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4996_, 0, v_c_4991_);
    v___x_4997_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4997_, 0, v_d_4993_);
    leanh::lean_ctor_set(v___x_4997_, 1, v___x_4995_);
    leanh::lean_ctor_set(v___x_4997_, 2, v___x_4996_);
    v___x_4998_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v___x_4997_);
    return v___x_4998_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder___boxed(
    mut v_c_4999_: *mut leanh::LeanObject,
    mut v_old2new_5000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5001_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_c_4999_, v_old2new_5000_);
    leanh::lean_dec_ref(v_old2new_5000_);
    return v_res_5001_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(
    mut v_c_5002_: *mut leanh::LeanObject,
    mut v_old2new_5003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_5004_ = leanh::lean_ctor_get(v_c_5002_, 0);
    leanh::lean_inc_ref(v_p_5004_);
    v___x_5005_ = l_Int_Linear_Poly_reorder(v_p_5004_, v_old2new_5003_);
    v___x_5006_ = leanh::lean_alloc_ctor(9, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5006_, 0, v_c_5002_);
    v___x_5007_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5007_, 0, v___x_5005_);
    leanh::lean_ctor_set(v___x_5007_, 1, v___x_5006_);
    v___x_5008_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_norm(v___x_5007_);
    return v___x_5008_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder___boxed(
    mut v_c_5009_: *mut leanh::LeanObject,
    mut v_old2new_5010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5011_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_c_5009_, v_old2new_5010_);
    leanh::lean_dec_ref(v_old2new_5010_);
    return v_res_5011_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(
    mut v_c_5012_: *mut leanh::LeanObject,
    mut v_old2new_5013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_5014_ = leanh::lean_ctor_get(v_c_5012_, 0);
    leanh::lean_inc_ref(v_p_5014_);
    v___x_5015_ = l_Int_Linear_Poly_reorder(v_p_5014_, v_old2new_5013_);
    v___x_5016_ = leanh::lean_alloc_ctor(16, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5016_, 0, v_c_5012_);
    v___x_5017_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5017_, 0, v___x_5015_);
    leanh::lean_ctor_set(v___x_5017_, 1, v___x_5016_);
    v___x_5018_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v___x_5017_);
    return v___x_5018_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder___boxed(
    mut v_c_5019_: *mut leanh::LeanObject,
    mut v_old2new_5020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5021_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_c_5019_, v_old2new_5020_);
    leanh::lean_dec_ref(v_old2new_5020_);
    return v_res_5021_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(
    mut v_c_5022_: *mut leanh::LeanObject,
    mut v_old2new_5023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_p_5024_ = leanh::lean_ctor_get(v_c_5022_, 0);
    leanh::lean_inc_ref(v_p_5024_);
    v___x_5025_ = l_Int_Linear_Poly_reorder(v_p_5024_, v_old2new_5023_);
    v___x_5026_ = leanh::lean_alloc_ctor(7, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5026_, 0, v_c_5022_);
    v___x_5027_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5027_, 0, v___x_5025_);
    leanh::lean_ctor_set(v___x_5027_, 1, v___x_5026_);
    v___x_5028_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_norm(v___x_5027_);
    return v___x_5028_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder___boxed(
    mut v_c_5029_: *mut leanh::LeanObject,
    mut v_old2new_5030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5031_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_c_5029_, v_old2new_5030_);
    leanh::lean_dec_ref(v_old2new_5030_);
    return v_res_5031_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(
    mut v_new2old_5032_: *mut leanh::LeanObject,
    mut v_inst_5033_: *mut leanh::LeanObject,
    mut v_m_5034_: *mut leanh::LeanObject,
    mut v_i_5035_: *mut leanh::LeanObject,
    mut v_h_5036_: *mut leanh::LeanObject,
    mut v_____s_5037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_j_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_j_5038_ = lean_array_fget_borrowed(v_new2old_5032_, v_i_5035_);
    v___x_5039_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_5033_, v_m_5034_, v_j_5038_);
    v_r_5040_ = l_Lean_PersistentArray_push___redArg(v_____s_5037_, v___x_5039_);
    v___x_5041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5041_, 0, v_r_5040_);
    return v___x_5041_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed(
    mut v_new2old_5042_: *mut leanh::LeanObject,
    mut v_inst_5043_: *mut leanh::LeanObject,
    mut v_m_5044_: *mut leanh::LeanObject,
    mut v_i_5045_: *mut leanh::LeanObject,
    mut v_h_5046_: *mut leanh::LeanObject,
    mut v_____s_5047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5048_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0(
        v_new2old_5042_,
        v_inst_5043_,
        v_m_5044_,
        v_i_5045_,
        v_h_5046_,
        v_____s_5047_,
    );
    leanh::lean_dec(v_i_5045_);
    leanh::lean_dec_ref(v_m_5044_);
    leanh::lean_dec(v_inst_5043_);
    leanh::lean_dec_ref(v_new2old_5042_);
    return v_res_5048_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5068_ = leanh::lean_unsigned_to_nat(32);
    v___x_5069_ = lean_mk_empty_array_with_capacity(v___x_5068_);
    v___x_5070_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5070_, 0, v___x_5069_);
    return v___x_5070_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5071_: usize = 0;
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5071_ = 5usize;
    v___x_5072_ = leanh::lean_unsigned_to_nat(0);
    v___x_5073_ = leanh::lean_unsigned_to_nat(32);
    v___x_5074_ = lean_mk_empty_array_with_capacity(v___x_5073_);
    v___x_5075_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__10,
    );
    v_r_5076_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v_r_5076_, 0, v___x_5075_);
    leanh::lean_ctor_set(v_r_5076_, 1, v___x_5074_);
    leanh::lean_ctor_set(v_r_5076_, 2, v___x_5072_);
    leanh::lean_ctor_set(v_r_5076_, 3, v___x_5072_);
    leanh::lean_ctor_set_usize(v_r_5076_, 4, v___x_5071_);
    return v_r_5076_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(
    mut v_inst_5077_: *mut leanh::LeanObject,
    mut v_m_5078_: *mut leanh::LeanObject,
    mut v_new2old_5079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_new2old_5079_);
    v___f_5080_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_5080_, 0, v_new2old_5079_);
    leanh::lean_closure_set(v___f_5080_, 1, v_inst_5077_);
    leanh::lean_closure_set(v___f_5080_, 2, v_m_5078_);
    v___x_5081_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__9;
    v___x_5082_ = leanh::lean_unsigned_to_nat(0);
    v_r_5083_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg___closed__11,
    );
    v___x_5084_ = lean_array_get_size(v_new2old_5079_);
    leanh::lean_dec_ref(v_new2old_5079_);
    v___x_5085_ = leanh::lean_unsigned_to_nat(1);
    v___x_5086_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_5086_, 0, v___x_5082_);
    leanh::lean_ctor_set(v___x_5086_, 1, v___x_5084_);
    leanh::lean_ctor_set(v___x_5086_, 2, v___x_5085_);
    v___x_5087_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5081_,
        v___x_5086_,
        v___f_5080_,
        v_r_5083_,
        v___x_5082_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5087_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap(
    mut v_00_u03b1_5088_: *mut leanh::LeanObject,
    mut v_inst_5089_: *mut leanh::LeanObject,
    mut v_m_5090_: *mut leanh::LeanObject,
    mut v_new2old_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5092_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(
        v_inst_5089_,
        v_m_5090_,
        v_new2old_5091_,
    );
    return v___x_5092_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_x_5093_: *mut leanh::LeanObject,
    mut v_x_5094_: *mut leanh::LeanObject,
    mut v_x_5095_: *mut leanh::LeanObject,
    mut v_x_5096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5101_: u8 = 0;
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5097_ = leanh::lean_ctor_get(v_x_5093_, 0);
                v_vs_5098_ = leanh::lean_ctor_get(v_x_5093_, 1);
                v_isSharedCheck_5122_ = (!leanh::lean_is_exclusive(v_x_5093_)) as u8;
                if v_isSharedCheck_5122_ == 0 {
                    v___x_5100_ = v_x_5093_;
                    v_isShared_5101_ = v_isSharedCheck_5122_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_5098_);
                    leanh::lean_inc(v_ks_5097_);
                    leanh::lean_dec(v_x_5093_);
                    v___x_5100_ = leanh::lean_box(0);
                    v_isShared_5101_ = v_isSharedCheck_5122_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5102_ = lean_array_get_size(v_ks_5097_);
                v___x_5103_ = lean_nat_dec_lt(v_x_5094_, v___x_5102_);
                if v___x_5103_ == 0 {
                    leanh::lean_dec(v_x_5094_);
                    v___x_5104_ = lean_array_push(v_ks_5097_, v_x_5095_);
                    v___x_5105_ = lean_array_push(v_vs_5098_, v_x_5096_);
                    if v_isShared_5101_ == 0 {
                        leanh::lean_ctor_set(v___x_5100_, 1, v___x_5105_);
                        leanh::lean_ctor_set(v___x_5100_, 0, v___x_5104_);
                        v___x_5107_ = v___x_5100_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5108_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 0, v___x_5104_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5108_, 1, v___x_5105_);
                        v___x_5107_ = v_reuseFailAlloc_5108_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5109_ = lean_array_fget_borrowed(v_ks_5097_, v_x_5094_);
                    v___x_5110_ = l_Int_Linear_instBEqPoly_beq(v_x_5095_, v_k_x27_5109_);
                    if v___x_5110_ == 0 {
                        if v_isShared_5101_ == 0 {
                            v___x_5112_ = v___x_5100_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5116_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_ks_5097_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5116_, 1, v_vs_5098_);
                            v___x_5112_ = v_reuseFailAlloc_5116_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5117_ = lean_array_fset(v_ks_5097_, v_x_5094_, v_x_5095_);
                        v___x_5118_ = lean_array_fset(v_vs_5098_, v_x_5094_, v_x_5096_);
                        leanh::lean_dec(v_x_5094_);
                        if v_isShared_5101_ == 0 {
                            leanh::lean_ctor_set(v___x_5100_, 1, v___x_5118_);
                            leanh::lean_ctor_set(v___x_5100_, 0, v___x_5117_);
                            v___x_5120_ = v___x_5100_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5121_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 0, v___x_5117_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5121_, 1, v___x_5118_);
                            v___x_5120_ = v_reuseFailAlloc_5121_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5107_;
            }
            3 => {
                v___x_5113_ = leanh::lean_unsigned_to_nat(1);
                v___x_5114_ = lean_nat_add(v_x_5094_, v___x_5113_);
                leanh::lean_dec(v_x_5094_);
                v_x_5093_ = v___x_5112_;
                v_x_5094_ = v___x_5114_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(
    mut v_n_5123_: *mut leanh::LeanObject,
    mut v_k_5124_: *mut leanh::LeanObject,
    mut v_v_5125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5126_ = leanh::lean_unsigned_to_nat(0);
    v___x_5127_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_n_5123_, v___x_5126_, v_k_5124_, v_v_5125_);
    return v___x_5127_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_5128_: usize = 0;
    let mut v___x_5129_: usize = 0;
    let mut v___x_5130_: usize = 0;
    v___x_5128_ = 5usize;
    v___x_5129_ = 1usize;
    v___x_5130_ = lean_usize_shift_left(v___x_5129_, v___x_5128_);
    return v___x_5130_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_5131_: usize = 0;
    let mut v___x_5132_: usize = 0;
    let mut v___x_5133_: usize = 0;
    v___x_5131_ = 1usize;
    v___x_5132_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__0);
    v___x_5133_ = lean_usize_sub(v___x_5132_, v___x_5131_);
    return v___x_5133_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5134_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5134_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(
    mut v_x_5135_: *mut leanh::LeanObject,
    mut v_x_5136_: usize,
    mut v_x_5137_: usize,
    mut v_x_5138_: *mut leanh::LeanObject,
    mut v_x_5139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: usize = 0;
    let mut v___x_5142_: usize = 0;
    let mut v___x_5143_: usize = 0;
    let mut v___x_5144_: usize = 0;
    let mut v_j_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v_v_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5164_: u8 = 0;
    let mut v___x_5165_: u8 = 0;
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut v_node_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5175_: u8 = 0;
    let mut v___x_5176_: usize = 0;
    let mut v___x_5177_: usize = 0;
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5182_: u8 = 0;
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v_unused_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5195_: u8 = 0;
    let mut v_ks_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: usize = 0;
    let mut v___x_5202_: u8 = 0;
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: u8 = 0;
    let mut v_reuseFailAlloc_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5135_) == 0 {
                    v_es_5140_ = leanh::lean_ctor_get(v_x_5135_, 0);
                    v___x_5141_ = 5usize;
                    v___x_5142_ = 1usize;
                    v___x_5143_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__1);
                    v___x_5144_ = lean_usize_land(v_x_5136_, v___x_5143_);
                    v_j_5145_ = lean_usize_to_nat(v___x_5144_);
                    v___x_5146_ = lean_array_get_size(v_es_5140_);
                    v___x_5147_ = lean_nat_dec_lt(v_j_5145_, v___x_5146_);
                    if v___x_5147_ == 0 {
                        leanh::lean_dec(v_j_5145_);
                        leanh::lean_dec(v_x_5139_);
                        leanh::lean_dec_ref(v_x_5138_);
                        return v_x_5135_;
                    } else {
                        leanh::lean_inc_ref(v_es_5140_);
                        v_isSharedCheck_5184_ = (!leanh::lean_is_exclusive(v_x_5135_)) as u8;
                        if v_isSharedCheck_5184_ == 0 {
                            v_unused_5185_ = leanh::lean_ctor_get(v_x_5135_, 0);
                            leanh::lean_dec(v_unused_5185_);
                            v___x_5149_ = v_x_5135_;
                            v_isShared_5150_ = v_isSharedCheck_5184_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_5135_);
                            v___x_5149_ = leanh::lean_box(0);
                            v_isShared_5150_ = v_isSharedCheck_5184_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5186_ = leanh::lean_ctor_get(v_x_5135_, 0);
                    v_vs_5187_ = leanh::lean_ctor_get(v_x_5135_, 1);
                    v_isSharedCheck_5207_ = (!leanh::lean_is_exclusive(v_x_5135_)) as u8;
                    if v_isSharedCheck_5207_ == 0 {
                        v___x_5189_ = v_x_5135_;
                        v_isShared_5190_ = v_isSharedCheck_5207_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5187_);
                        leanh::lean_inc(v_ks_5186_);
                        leanh::lean_dec(v_x_5135_);
                        v___x_5189_ = leanh::lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5207_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5151_ = lean_array_fget(v_es_5140_, v_j_5145_);
                v___x_5152_ = leanh::lean_box(0);
                v_xs_x27_5153_ = lean_array_fset(v_es_5140_, v_j_5145_, v___x_5152_);
                match leanh::lean_obj_tag(v_v_5151_) {
                    0 => {
                        v_key_5160_ = leanh::lean_ctor_get(v_v_5151_, 0);
                        v_val_5161_ = leanh::lean_ctor_get(v_v_5151_, 1);
                        v_isSharedCheck_5171_ = (!leanh::lean_is_exclusive(v_v_5151_)) as u8;
                        if v_isSharedCheck_5171_ == 0 {
                            v___x_5163_ = v_v_5151_;
                            v_isShared_5164_ = v_isSharedCheck_5171_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_5161_);
                            leanh::lean_inc(v_key_5160_);
                            leanh::lean_dec(v_v_5151_);
                            v___x_5163_ = leanh::lean_box(0);
                            v_isShared_5164_ = v_isSharedCheck_5171_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5172_ = leanh::lean_ctor_get(v_v_5151_, 0);
                        v_isSharedCheck_5182_ = (!leanh::lean_is_exclusive(v_v_5151_)) as u8;
                        if v_isSharedCheck_5182_ == 0 {
                            v___x_5174_ = v_v_5151_;
                            v_isShared_5175_ = v_isSharedCheck_5182_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_5172_);
                            leanh::lean_dec(v_v_5151_);
                            v___x_5174_ = leanh::lean_box(0);
                            v_isShared_5175_ = v_isSharedCheck_5182_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5183_, 0, v_x_5138_);
                        leanh::lean_ctor_set(v___x_5183_, 1, v_x_5139_);
                        v___y_5155_ = v___x_5183_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5156_ = lean_array_fset(v_xs_x27_5153_, v_j_5145_, v___y_5155_);
                leanh::lean_dec(v_j_5145_);
                if v_isShared_5150_ == 0 {
                    leanh::lean_ctor_set(v___x_5149_, 0, v___x_5156_);
                    v___x_5158_ = v___x_5149_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5159_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5156_);
                    v___x_5158_ = v_reuseFailAlloc_5159_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5158_;
            }
            4 => {
                v___x_5165_ = l_Int_Linear_instBEqPoly_beq(v_x_5138_, v_key_5160_);
                if v___x_5165_ == 0 {
                    leanh::lean_del_object(v___x_5163_);
                    v___x_5166_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5160_,
                        v_val_5161_,
                        v_x_5138_,
                        v_x_5139_,
                    );
                    v___x_5167_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5167_, 0, v___x_5166_);
                    v___y_5155_ = v___x_5167_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_5161_);
                    leanh::lean_dec(v_key_5160_);
                    if v_isShared_5164_ == 0 {
                        leanh::lean_ctor_set(v___x_5163_, 1, v_x_5139_);
                        leanh::lean_ctor_set(v___x_5163_, 0, v_x_5138_);
                        v___x_5169_ = v___x_5163_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5170_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_x_5138_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5170_, 1, v_x_5139_);
                        v___x_5169_ = v_reuseFailAlloc_5170_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5155_ = v___x_5169_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5176_ = lean_usize_shift_right(v_x_5136_, v___x_5141_);
                v___x_5177_ = lean_usize_add(v_x_5137_, v___x_5142_);
                v___x_5178_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_node_5172_, v___x_5176_, v___x_5177_, v_x_5138_, v_x_5139_);
                if v_isShared_5175_ == 0 {
                    leanh::lean_ctor_set(v___x_5174_, 0, v___x_5178_);
                    v___x_5180_ = v___x_5174_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5181_, 0, v___x_5178_);
                    v___x_5180_ = v_reuseFailAlloc_5181_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5155_ = v___x_5180_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5190_ == 0 {
                    v___x_5192_ = v___x_5189_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5206_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_ks_5186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5206_, 1, v_vs_5187_);
                    v___x_5192_ = v_reuseFailAlloc_5206_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5193_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v___x_5192_, v_x_5138_, v_x_5139_);
                v___x_5201_ = 7usize;
                v___x_5202_ = lean_usize_dec_le(v___x_5201_, v_x_5137_);
                if v___x_5202_ == 0 {
                    v___x_5203_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5193_);
                    v___x_5204_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5205_ = lean_nat_dec_lt(v___x_5203_, v___x_5204_);
                    leanh::lean_dec(v___x_5203_);
                    v___y_5195_ = v___x_5205_;
                    state = 10;
                    continue;
                } else {
                    v___y_5195_ = v___x_5202_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5195_ == 0 {
                    v_ks_5196_ = leanh::lean_ctor_get(v_newNode_5193_, 0);
                    leanh::lean_inc_ref(v_ks_5196_);
                    v_vs_5197_ = leanh::lean_ctor_get(v_newNode_5193_, 1);
                    leanh::lean_inc_ref(v_vs_5197_);
                    leanh::lean_dec_ref(v_newNode_5193_);
                    v___x_5198_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5199_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___closed__2);
                    v___x_5200_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_x_5137_, v_ks_5196_, v_vs_5197_, v___x_5198_, v___x_5199_);
                    leanh::lean_dec_ref(v_vs_5197_);
                    leanh::lean_dec_ref(v_ks_5196_);
                    return v___x_5200_;
                } else {
                    return v_newNode_5193_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(
    mut v_depth_5208_: usize,
    mut v_keys_5209_: *mut leanh::LeanObject,
    mut v_vals_5210_: *mut leanh::LeanObject,
    mut v_i_5211_: *mut leanh::LeanObject,
    mut v_entries_5212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: u8 = 0;
    let mut v_k_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: u64 = 0;
    let mut v_h_5218_: usize = 0;
    let mut v___x_5219_: usize = 0;
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: usize = 0;
    let mut v___x_5222_: usize = 0;
    let mut v___x_5223_: usize = 0;
    let mut v_h_5224_: usize = 0;
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5213_ = lean_array_get_size(v_keys_5209_);
                v___x_5214_ = lean_nat_dec_lt(v_i_5211_, v___x_5213_);
                if v___x_5214_ == 0 {
                    leanh::lean_dec(v_i_5211_);
                    return v_entries_5212_;
                } else {
                    v_k_5215_ = lean_array_fget_borrowed(v_keys_5209_, v_i_5211_);
                    v_v_5216_ = lean_array_fget_borrowed(v_vals_5210_, v_i_5211_);
                    v___x_5217_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_k_5215_);
                    v_h_5218_ = lean_uint64_to_usize(v___x_5217_);
                    v___x_5219_ = 5usize;
                    v___x_5220_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5221_ = 1usize;
                    v___x_5222_ = lean_usize_sub(v_depth_5208_, v___x_5221_);
                    v___x_5223_ = lean_usize_mul(v___x_5219_, v___x_5222_);
                    v_h_5224_ = lean_usize_shift_right(v_h_5218_, v___x_5223_);
                    v___x_5225_ = lean_nat_add(v_i_5211_, v___x_5220_);
                    leanh::lean_dec(v_i_5211_);
                    leanh::lean_inc(v_v_5216_);
                    leanh::lean_inc(v_k_5215_);
                    v___x_5226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_entries_5212_, v_h_5224_, v_depth_5208_, v_k_5215_, v_v_5216_);
                    v_i_5211_ = v___x_5225_;
                    v_entries_5212_ = v___x_5226_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_5228_: *mut leanh::LeanObject,
    mut v_keys_5229_: *mut leanh::LeanObject,
    mut v_vals_5230_: *mut leanh::LeanObject,
    mut v_i_5231_: *mut leanh::LeanObject,
    mut v_entries_5232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5233_: usize = 0;
    let mut v_res_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5233_ = leanh::lean_unbox_usize(v_depth_5228_);
    leanh::lean_dec(v_depth_5228_);
    v_res_5234_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_boxed_5233_, v_keys_5229_, v_vals_5230_, v_i_5231_, v_entries_5232_);
    leanh::lean_dec_ref(v_vals_5230_);
    leanh::lean_dec_ref(v_keys_5229_);
    return v_res_5234_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg___boxed(
    mut v_x_5235_: *mut leanh::LeanObject,
    mut v_x_5236_: *mut leanh::LeanObject,
    mut v_x_5237_: *mut leanh::LeanObject,
    mut v_x_5238_: *mut leanh::LeanObject,
    mut v_x_5239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1894__boxed_5240_: usize = 0;
    let mut v_x_1895__boxed_5241_: usize = 0;
    let mut v_res_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1894__boxed_5240_ = leanh::lean_unbox_usize(v_x_5236_);
    leanh::lean_dec(v_x_5236_);
    v_x_1895__boxed_5241_ = leanh::lean_unbox_usize(v_x_5237_);
    leanh::lean_dec(v_x_5237_);
    v_res_5242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_5235_, v_x_1894__boxed_5240_, v_x_1895__boxed_5241_, v_x_5238_, v_x_5239_);
    return v_res_5242_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(
    mut v_x_5243_: *mut leanh::LeanObject,
    mut v_x_5244_: *mut leanh::LeanObject,
    mut v_x_5245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5246_: u64 = 0;
    let mut v___x_5247_: usize = 0;
    let mut v___x_5248_: usize = 0;
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5246_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_5244_);
    v___x_5247_ = lean_uint64_to_usize(v___x_5246_);
    v___x_5248_ = 1usize;
    v___x_5249_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_5243_, v___x_5247_, v___x_5248_, v_x_5244_, v_x_5245_);
    return v___x_5249_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(
    mut v_old2new_5250_: *mut leanh::LeanObject,
    mut v_x_5251_: *mut leanh::LeanObject,
    mut v_____s_5252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_x27_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_5253_ = leanh::lean_ctor_get(v_x_5251_, 0);
    leanh::lean_inc(v_fst_5253_);
    v_snd_5254_ = leanh::lean_ctor_get(v_x_5251_, 1);
    leanh::lean_inc(v_snd_5254_);
    leanh::lean_dec_ref(v_x_5251_);
    v___x_5255_ = l_Int_Linear_Poly_reorder(v_fst_5253_, v_old2new_5250_);
    v_m_x27_5256_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_____s_5252_, v___x_5255_, v_snd_5254_);
    v___x_5257_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5257_, 0, v_m_x27_5256_);
    return v___x_5257_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed(
    mut v_old2new_5258_: *mut leanh::LeanObject,
    mut v_x_5259_: *mut leanh::LeanObject,
    mut v_____s_5260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5261_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0(
        v_old2new_5258_,
        v_x_5259_,
        v_____s_5260_,
    );
    leanh::lean_dec_ref(v_old2new_5258_);
    return v_res_5261_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(
    mut v_f_5262_: *mut leanh::LeanObject,
    mut v_keys_5263_: *mut leanh::LeanObject,
    mut v_vals_5264_: *mut leanh::LeanObject,
    mut v_i_5265_: *mut leanh::LeanObject,
    mut v_acc_5266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: u8 = 0;
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5267_ = lean_array_get_size(v_keys_5263_);
                v___x_5268_ = lean_nat_dec_lt(v_i_5265_, v___x_5267_);
                if v___x_5268_ == 0 {
                    leanh::lean_dec(v_i_5265_);
                    leanh::lean_dec_ref(v_f_5262_);
                    v___x_5269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5269_, 0, v_acc_5266_);
                    return v___x_5269_;
                } else {
                    v_k_5270_ = lean_array_fget_borrowed(v_keys_5263_, v_i_5265_);
                    v_v_5271_ = lean_array_fget_borrowed(v_vals_5264_, v_i_5265_);
                    leanh::lean_inc_ref(v_f_5262_);
                    leanh::lean_inc(v_v_5271_);
                    leanh::lean_inc(v_k_5270_);
                    v___x_5272_ =
                        leanh::lean_apply_3(v_f_5262_, v_acc_5266_, v_k_5270_, v_v_5271_);
                    if leanh::lean_obj_tag(v___x_5272_) == 0 {
                        leanh::lean_dec(v_i_5265_);
                        leanh::lean_dec_ref(v_f_5262_);
                        return v___x_5272_;
                    } else {
                        v_a_5273_ = leanh::lean_ctor_get(v___x_5272_, 0);
                        leanh::lean_inc(v_a_5273_);
                        leanh::lean_dec_ref_known(v___x_5272_, 1);
                        v___x_5274_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5275_ = lean_nat_add(v_i_5265_, v___x_5274_);
                        leanh::lean_dec(v_i_5265_);
                        v_i_5265_ = v___x_5275_;
                        v_acc_5266_ = v_a_5273_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_f_5277_: *mut leanh::LeanObject,
    mut v_keys_5278_: *mut leanh::LeanObject,
    mut v_vals_5279_: *mut leanh::LeanObject,
    mut v_i_5280_: *mut leanh::LeanObject,
    mut v_acc_5281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_5277_, v_keys_5278_, v_vals_5279_, v_i_5280_, v_acc_5281_);
    leanh::lean_dec_ref(v_vals_5279_);
    leanh::lean_dec_ref(v_keys_5278_);
    return v_res_5282_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(
    mut v_f_5283_: *mut leanh::LeanObject,
    mut v_x_5284_: *mut leanh::LeanObject,
    mut v_x_5285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: u8 = 0;
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: u8 = 0;
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: usize = 0;
    let mut v___x_5301_: usize = 0;
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: usize = 0;
    let mut v___x_5304_: usize = 0;
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5306_: u8 = 0;
    let mut v_ks_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5284_) == 0 {
                    v_es_5286_ = leanh::lean_ctor_get(v_x_5284_, 0);
                    v_isSharedCheck_5306_ = (!leanh::lean_is_exclusive(v_x_5284_)) as u8;
                    if v_isSharedCheck_5306_ == 0 {
                        v___x_5288_ = v_x_5284_;
                        v_isShared_5289_ = v_isSharedCheck_5306_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_5286_);
                        leanh::lean_dec(v_x_5284_);
                        v___x_5288_ = leanh::lean_box(0);
                        v_isShared_5289_ = v_isSharedCheck_5306_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_5307_ = leanh::lean_ctor_get(v_x_5284_, 0);
                    leanh::lean_inc_ref(v_ks_5307_);
                    v_vs_5308_ = leanh::lean_ctor_get(v_x_5284_, 1);
                    leanh::lean_inc_ref(v_vs_5308_);
                    leanh::lean_dec_ref_known(v_x_5284_, 2);
                    v___x_5309_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_5283_, v_ks_5307_, v_vs_5308_, v___x_5309_, v_x_5285_);
                    leanh::lean_dec_ref(v_vs_5308_);
                    leanh::lean_dec_ref(v_ks_5307_);
                    return v___x_5310_;
                }
            }
            1 => {
                v___x_5290_ = leanh::lean_unsigned_to_nat(0);
                v___x_5291_ = lean_array_get_size(v_es_5286_);
                v___x_5292_ = lean_nat_dec_lt(v___x_5290_, v___x_5291_);
                if v___x_5292_ == 0 {
                    leanh::lean_dec_ref(v_es_5286_);
                    leanh::lean_dec_ref(v_f_5283_);
                    if v_isShared_5289_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5288_, 1);
                        leanh::lean_ctor_set(v___x_5288_, 0, v_x_5285_);
                        v___x_5294_ = v___x_5288_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_x_5285_);
                        v___x_5294_ = v_reuseFailAlloc_5295_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5296_ = lean_nat_dec_le(v___x_5291_, v___x_5291_);
                    if v___x_5296_ == 0 {
                        if v___x_5292_ == 0 {
                            leanh::lean_dec_ref(v_es_5286_);
                            leanh::lean_dec_ref(v_f_5283_);
                            if v_isShared_5289_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_5288_, 1);
                                leanh::lean_ctor_set(v___x_5288_, 0, v_x_5285_);
                                v___x_5298_ = v___x_5288_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5299_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_x_5285_);
                                v___x_5298_ = v_reuseFailAlloc_5299_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_5288_);
                            v___x_5300_ = 0usize;
                            v___x_5301_ = lean_usize_of_nat(v___x_5291_);
                            v___x_5302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_5283_, v_es_5286_, v___x_5300_, v___x_5301_, v_x_5285_);
                            leanh::lean_dec_ref(v_es_5286_);
                            return v___x_5302_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_5288_);
                        v___x_5303_ = 0usize;
                        v___x_5304_ = lean_usize_of_nat(v___x_5291_);
                        v___x_5305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_5283_, v_es_5286_, v___x_5303_, v___x_5304_, v_x_5285_);
                        leanh::lean_dec_ref(v_es_5286_);
                        return v___x_5305_;
                    }
                }
            }
            2 => {
                return v___x_5294_;
            }
            3 => {
                return v___x_5298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(
    mut v_f_5311_: *mut leanh::LeanObject,
    mut v_as_5312_: *mut leanh::LeanObject,
    mut v_i_5313_: usize,
    mut v_stop_5314_: usize,
    mut v_b_5315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: usize = 0;
    let mut v___x_5319_: usize = 0;
    let mut v___y_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: u8 = 0;
    let mut v___x_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5324_ = lean_usize_dec_eq(v_i_5313_, v_stop_5314_);
                if v___x_5324_ == 0 {
                    v___x_5325_ = lean_array_uget_borrowed(v_as_5312_, v_i_5313_);
                    match leanh::lean_obj_tag(v___x_5325_) {
                        0 => {
                            v_key_5326_ = leanh::lean_ctor_get(v___x_5325_, 0);
                            v_val_5327_ = leanh::lean_ctor_get(v___x_5325_, 1);
                            leanh::lean_inc_ref(v_f_5311_);
                            leanh::lean_inc(v_val_5327_);
                            leanh::lean_inc(v_key_5326_);
                            v___x_5328_ = leanh::lean_apply_3(
                                v_f_5311_,
                                v_b_5315_,
                                v_key_5326_,
                                v_val_5327_,
                            );
                            v___y_5322_ = v___x_5328_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_5329_ = leanh::lean_ctor_get(v___x_5325_, 0);
                            leanh::lean_inc(v_node_5329_);
                            leanh::lean_inc_ref(v_f_5311_);
                            v___x_5330_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_5311_, v_node_5329_, v_b_5315_);
                            v___y_5322_ = v___x_5330_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_5317_ = v_b_5315_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_f_5311_);
                    v___x_5331_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5331_, 0, v_b_5315_);
                    return v___x_5331_;
                }
            }
            1 => {
                v___x_5318_ = 1usize;
                v___x_5319_ = lean_usize_add(v_i_5313_, v___x_5318_);
                v_i_5313_ = v___x_5319_;
                v_b_5315_ = v_a_5317_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_5322_) == 0 {
                    leanh::lean_dec_ref(v_f_5311_);
                    return v___y_5322_;
                } else {
                    v_a_5323_ = leanh::lean_ctor_get(v___y_5322_, 0);
                    leanh::lean_inc(v_a_5323_);
                    leanh::lean_dec_ref_known(v___y_5322_, 1);
                    v_a_5317_ = v_a_5323_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg___boxed(
    mut v_f_5332_: *mut leanh::LeanObject,
    mut v_as_5333_: *mut leanh::LeanObject,
    mut v_i_5334_: *mut leanh::LeanObject,
    mut v_stop_5335_: *mut leanh::LeanObject,
    mut v_b_5336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5337_: usize = 0;
    let mut v_stop_boxed_5338_: usize = 0;
    let mut v_res_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5337_ = leanh::lean_unbox_usize(v_i_5334_);
    leanh::lean_dec(v_i_5334_);
    v_stop_boxed_5338_ = leanh::lean_unbox_usize(v_stop_5335_);
    leanh::lean_dec(v_stop_5335_);
    v_res_5339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_5332_, v_as_5333_, v_i_boxed_5337_, v_stop_boxed_5338_, v_b_5336_);
    leanh::lean_dec_ref(v_as_5333_);
    return v_res_5339_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0(
    mut v_f_5340_: *mut leanh::LeanObject,
    mut v_s_5341_: *mut leanh::LeanObject,
    mut v_a_5342_: *mut leanh::LeanObject,
    mut v_b_5343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5349_: u8 = 0;
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5353_: u8 = 0;
    let mut v_a_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5357_: u8 = 0;
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5344_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5344_, 0, v_a_5342_);
                leanh::lean_ctor_set(v___x_5344_, 1, v_b_5343_);
                v___x_5345_ = leanh::lean_apply_2(v_f_5340_, v___x_5344_, v_s_5341_);
                if leanh::lean_obj_tag(v___x_5345_) == 0 {
                    v_a_5346_ = leanh::lean_ctor_get(v___x_5345_, 0);
                    v_isSharedCheck_5353_ = (!leanh::lean_is_exclusive(v___x_5345_)) as u8;
                    if v_isSharedCheck_5353_ == 0 {
                        v___x_5348_ = v___x_5345_;
                        v_isShared_5349_ = v_isSharedCheck_5353_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5346_);
                        leanh::lean_dec(v___x_5345_);
                        v___x_5348_ = leanh::lean_box(0);
                        v_isShared_5349_ = v_isSharedCheck_5353_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5354_ = leanh::lean_ctor_get(v___x_5345_, 0);
                    v_isSharedCheck_5361_ = (!leanh::lean_is_exclusive(v___x_5345_)) as u8;
                    if v_isSharedCheck_5361_ == 0 {
                        v___x_5356_ = v___x_5345_;
                        v_isShared_5357_ = v_isSharedCheck_5361_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5354_);
                        leanh::lean_dec(v___x_5345_);
                        v___x_5356_ = leanh::lean_box(0);
                        v_isShared_5357_ = v_isSharedCheck_5361_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5349_ == 0 {
                    v___x_5351_ = v___x_5348_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5352_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
                    v___x_5351_ = v_reuseFailAlloc_5352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5351_;
            }
            3 => {
                if v_isShared_5357_ == 0 {
                    v___x_5359_ = v___x_5356_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5360_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_a_5354_);
                    v___x_5359_ = v_reuseFailAlloc_5360_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(
    mut v_map_5362_: *mut leanh::LeanObject,
    mut v_init_5363_: *mut leanh::LeanObject,
    mut v_f_5364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5365_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_5365_, 0, v_f_5364_);
    leanh::lean_inc_ref(v_map_5362_);
    v___x_5366_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v___f_5365_, v_map_5362_, v_init_5363_);
    v_a_5367_ = leanh::lean_ctor_get(v___x_5366_, 0);
    leanh::lean_inc(v_a_5367_);
    leanh::lean_dec_ref(v___x_5366_);
    return v_a_5367_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg___boxed(
    mut v_map_5368_: *mut leanh::LeanObject,
    mut v_init_5369_: *mut leanh::LeanObject,
    mut v_f_5370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5371_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_5368_, v_init_5369_, v_f_5370_);
    leanh::lean_dec_ref(v_map_5368_);
    return v_res_5371_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5372_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5372_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_x27_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__0,
    );
    v_m_x27_5374_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v_m_x27_5374_, 0, v___x_5373_);
    return v_m_x27_5374_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(
    mut v_m_5375_: *mut leanh::LeanObject,
    mut v_old2new_5376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_x27_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5377_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_5377_, 0, v_old2new_5376_);
    v_m_x27_5378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1,
    );
    v___x_5379_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_m_5375_, v_m_x27_5378_, v___f_5377_);
    return v___x_5379_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___boxed(
    mut v_m_5380_: *mut leanh::LeanObject,
    mut v_old2new_5381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5382_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits(v_m_5380_, v_old2new_5381_);
    leanh::lean_dec_ref(v_m_5380_);
    return v_res_5382_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0(
    mut v_00_u03b2_5383_: *mut leanh::LeanObject,
    mut v_x_5384_: *mut leanh::LeanObject,
    mut v_x_5385_: *mut leanh::LeanObject,
    mut v_x_5386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5387_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0___redArg(v_x_5384_, v_x_5385_, v_x_5386_);
    return v___x_5387_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(
    mut v_00_u03c3_5388_: *mut leanh::LeanObject,
    mut v_00_u03b2_5389_: *mut leanh::LeanObject,
    mut v_map_5390_: *mut leanh::LeanObject,
    mut v_init_5391_: *mut leanh::LeanObject,
    mut v_f_5392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5393_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___redArg(v_map_5390_, v_init_5391_, v_f_5392_);
    return v___x_5393_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1___boxed(
    mut v_00_u03c3_5394_: *mut leanh::LeanObject,
    mut v_00_u03b2_5395_: *mut leanh::LeanObject,
    mut v_map_5396_: *mut leanh::LeanObject,
    mut v_init_5397_: *mut leanh::LeanObject,
    mut v_f_5398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5399_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1(v_00_u03c3_5394_, v_00_u03b2_5395_, v_map_5396_, v_init_5397_, v_f_5398_);
    leanh::lean_dec_ref(v_map_5396_);
    return v_res_5399_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(
    mut v_00_u03b2_5400_: *mut leanh::LeanObject,
    mut v_x_5401_: *mut leanh::LeanObject,
    mut v_x_5402_: usize,
    mut v_x_5403_: usize,
    mut v_x_5404_: *mut leanh::LeanObject,
    mut v_x_5405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5406_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___redArg(v_x_5401_, v_x_5402_, v_x_5403_, v_x_5404_, v_x_5405_);
    return v___x_5406_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0___boxed(
    mut v_00_u03b2_5407_: *mut leanh::LeanObject,
    mut v_x_5408_: *mut leanh::LeanObject,
    mut v_x_5409_: *mut leanh::LeanObject,
    mut v_x_5410_: *mut leanh::LeanObject,
    mut v_x_5411_: *mut leanh::LeanObject,
    mut v_x_5412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2251__boxed_5413_: usize = 0;
    let mut v_x_2252__boxed_5414_: usize = 0;
    let mut v_res_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2251__boxed_5413_ = leanh::lean_unbox_usize(v_x_5409_);
    leanh::lean_dec(v_x_5409_);
    v_x_2252__boxed_5414_ = leanh::lean_unbox_usize(v_x_5410_);
    leanh::lean_dec(v_x_5410_);
    v_res_5415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0(v_00_u03b2_5407_, v_x_5408_, v_x_2251__boxed_5413_, v_x_2252__boxed_5414_, v_x_5411_, v_x_5412_);
    return v_res_5415_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2___redArg(
    mut v_map_5416_: *mut leanh::LeanObject,
    mut v_f_5417_: *mut leanh::LeanObject,
    mut v_init_5418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5419_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_5417_, v_map_5416_, v_init_5418_);
    return v___x_5419_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2(
    mut v_00_u03c3_5420_: *mut leanh::LeanObject,
    mut v_00_u03c3_5421_: *mut leanh::LeanObject,
    mut v_00_u03b2_5422_: *mut leanh::LeanObject,
    mut v_map_5423_: *mut leanh::LeanObject,
    mut v_f_5424_: *mut leanh::LeanObject,
    mut v_init_5425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5426_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_5424_, v_map_5423_, v_init_5425_);
    return v___x_5426_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5427_: *mut leanh::LeanObject,
    mut v_n_5428_: *mut leanh::LeanObject,
    mut v_k_5429_: *mut leanh::LeanObject,
    mut v_v_5430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5431_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1___redArg(v_n_5428_, v_k_5429_, v_v_5430_);
    return v___x_5431_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5432_: *mut leanh::LeanObject,
    mut v_depth_5433_: usize,
    mut v_keys_5434_: *mut leanh::LeanObject,
    mut v_vals_5435_: *mut leanh::LeanObject,
    mut v_heq_5436_: *mut leanh::LeanObject,
    mut v_i_5437_: *mut leanh::LeanObject,
    mut v_entries_5438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___redArg(v_depth_5433_, v_keys_5434_, v_vals_5435_, v_i_5437_, v_entries_5438_);
    return v___x_5439_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5440_: *mut leanh::LeanObject,
    mut v_depth_5441_: *mut leanh::LeanObject,
    mut v_keys_5442_: *mut leanh::LeanObject,
    mut v_vals_5443_: *mut leanh::LeanObject,
    mut v_heq_5444_: *mut leanh::LeanObject,
    mut v_i_5445_: *mut leanh::LeanObject,
    mut v_entries_5446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5447_: usize = 0;
    let mut v_res_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5447_ = leanh::lean_unbox_usize(v_depth_5441_);
    leanh::lean_dec(v_depth_5441_);
    v_res_5448_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__2(v_00_u03b2_5440_, v_depth_boxed_5447_, v_keys_5442_, v_vals_5443_, v_heq_5444_, v_i_5445_, v_entries_5446_);
    leanh::lean_dec_ref(v_vals_5443_);
    leanh::lean_dec_ref(v_keys_5442_);
    return v_res_5448_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5(
    mut v_00_u03c3_5449_: *mut leanh::LeanObject,
    mut v_00_u03c3_5450_: *mut leanh::LeanObject,
    mut v_00_u03b1_5451_: *mut leanh::LeanObject,
    mut v_00_u03b2_5452_: *mut leanh::LeanObject,
    mut v_f_5453_: *mut leanh::LeanObject,
    mut v_x_5454_: *mut leanh::LeanObject,
    mut v_x_5455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5456_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5___redArg(v_f_5453_, v_x_5454_, v_x_5455_);
    return v___x_5456_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_5457_: *mut leanh::LeanObject,
    mut v_x_5458_: *mut leanh::LeanObject,
    mut v_x_5459_: *mut leanh::LeanObject,
    mut v_x_5460_: *mut leanh::LeanObject,
    mut v_x_5461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5462_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__0_spec__0_spec__1_spec__3___redArg(v_x_5458_, v_x_5459_, v_x_5460_, v_x_5461_);
    return v___x_5462_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(
    mut v_00_u03b1_5463_: *mut leanh::LeanObject,
    mut v_00_u03b2_5464_: *mut leanh::LeanObject,
    mut v_00_u03c3_5465_: *mut leanh::LeanObject,
    mut v_00_u03c3_5466_: *mut leanh::LeanObject,
    mut v_f_5467_: *mut leanh::LeanObject,
    mut v_as_5468_: *mut leanh::LeanObject,
    mut v_i_5469_: usize,
    mut v_stop_5470_: usize,
    mut v_b_5471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___redArg(v_f_5467_, v_as_5468_, v_i_5469_, v_stop_5470_, v_b_5471_);
    return v___x_5472_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7___boxed(
    mut v_00_u03b1_5473_: *mut leanh::LeanObject,
    mut v_00_u03b2_5474_: *mut leanh::LeanObject,
    mut v_00_u03c3_5475_: *mut leanh::LeanObject,
    mut v_00_u03c3_5476_: *mut leanh::LeanObject,
    mut v_f_5477_: *mut leanh::LeanObject,
    mut v_as_5478_: *mut leanh::LeanObject,
    mut v_i_5479_: *mut leanh::LeanObject,
    mut v_stop_5480_: *mut leanh::LeanObject,
    mut v_b_5481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5482_: usize = 0;
    let mut v_stop_boxed_5483_: usize = 0;
    let mut v_res_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5482_ = leanh::lean_unbox_usize(v_i_5479_);
    leanh::lean_dec(v_i_5479_);
    v_stop_boxed_5483_ = leanh::lean_unbox_usize(v_stop_5480_);
    leanh::lean_dec(v_stop_5480_);
    v_res_5484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__7(v_00_u03b1_5473_, v_00_u03b2_5474_, v_00_u03c3_5475_, v_00_u03c3_5476_, v_f_5477_, v_as_5478_, v_i_boxed_5482_, v_stop_boxed_5483_, v_b_5481_);
    leanh::lean_dec_ref(v_as_5478_);
    return v_res_5484_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(
    mut v_00_u03c3_5485_: *mut leanh::LeanObject,
    mut v_00_u03c3_5486_: *mut leanh::LeanObject,
    mut v_00_u03b1_5487_: *mut leanh::LeanObject,
    mut v_00_u03b2_5488_: *mut leanh::LeanObject,
    mut v_f_5489_: *mut leanh::LeanObject,
    mut v_keys_5490_: *mut leanh::LeanObject,
    mut v_vals_5491_: *mut leanh::LeanObject,
    mut v_heq_5492_: *mut leanh::LeanObject,
    mut v_i_5493_: *mut leanh::LeanObject,
    mut v_acc_5494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5495_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___redArg(v_f_5489_, v_keys_5490_, v_vals_5491_, v_i_5493_, v_acc_5494_);
    return v___x_5495_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03c3_5496_: *mut leanh::LeanObject,
    mut v_00_u03c3_5497_: *mut leanh::LeanObject,
    mut v_00_u03b1_5498_: *mut leanh::LeanObject,
    mut v_00_u03b2_5499_: *mut leanh::LeanObject,
    mut v_f_5500_: *mut leanh::LeanObject,
    mut v_keys_5501_: *mut leanh::LeanObject,
    mut v_vals_5502_: *mut leanh::LeanObject,
    mut v_heq_5503_: *mut leanh::LeanObject,
    mut v_i_5504_: *mut leanh::LeanObject,
    mut v_acc_5505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits_spec__1_spec__2_spec__5_spec__8(v_00_u03c3_5496_, v_00_u03c3_5497_, v_00_u03b1_5498_, v_00_u03b2_5499_, v_f_5500_, v_keys_5501_, v_vals_5502_, v_heq_5503_, v_i_5504_, v_acc_5505_);
    leanh::lean_dec_ref(v_vals_5502_);
    leanh::lean_dec_ref(v_keys_5501_);
    return v_res_5506_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(
    mut v___x_5507_: *mut leanh::LeanObject,
    mut v_x_5508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5509_ = leanh::lean_unsigned_to_nat(0);
    v___x_5510_ = lean_array_get_borrowed(v___x_5509_, v___x_5507_, v_x_5508_);
    leanh::lean_inc(v___x_5510_);
    return v___x_5510_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed(
    mut v___x_5511_: *mut leanh::LeanObject,
    mut v_x_5512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5513_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0(v___x_5511_, v_x_5512_);
    leanh::lean_dec(v_x_5512_);
    leanh::lean_dec_ref(v___x_5511_);
    return v_res_5513_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0(
    mut v_f_5514_: *mut leanh::LeanObject,
    mut v_x_5515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5516_ = leanh::lean_apply_1(v_f_5514_, v_x_5515_);
    return v___x_5516_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(
    mut v_f_5517_: *mut leanh::LeanObject,
    mut v_as_5518_: *mut leanh::LeanObject,
    mut v_i_5519_: *mut leanh::LeanObject,
    mut v_acc_5520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: u8 = 0;
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5521_ = lean_array_get_size(v_as_5518_);
                v___x_5522_ = lean_nat_dec_eq(v_i_5519_, v___x_5521_);
                if v___x_5522_ == 0 {
                    v___x_5523_ = lean_array_fget_borrowed(v_as_5518_, v_i_5519_);
                    leanh::lean_inc(v_f_5517_);
                    leanh::lean_inc(v___x_5523_);
                    v___x_5524_ = leanh::lean_apply_1(v_f_5517_, v___x_5523_);
                    v___x_5525_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5526_ = lean_nat_add(v_i_5519_, v___x_5525_);
                    leanh::lean_dec(v_i_5519_);
                    v___x_5527_ = lean_array_push(v_acc_5520_, v___x_5524_);
                    v_i_5519_ = v___x_5526_;
                    v_acc_5520_ = v___x_5527_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_i_5519_);
                    leanh::lean_dec(v_f_5517_);
                    return v_acc_5520_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg___boxed(
    mut v_f_5529_: *mut leanh::LeanObject,
    mut v_as_5530_: *mut leanh::LeanObject,
    mut v_i_5531_: *mut leanh::LeanObject,
    mut v_acc_5532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5533_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_5529_, v_as_5530_, v_i_5531_, v_acc_5532_);
    leanh::lean_dec_ref(v_as_5530_);
    return v_res_5533_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(
    mut v_f_5534_: *mut leanh::LeanObject,
    mut v_as_5535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5536_ = leanh::lean_unsigned_to_nat(0);
    v___x_5537_ = lean_array_get_size(v_as_5535_);
    v___x_5538_ = lean_mk_empty_array_with_capacity(v___x_5537_);
    v___x_5539_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_5534_, v_as_5535_, v___x_5536_, v___x_5538_);
    return v___x_5539_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg___boxed(
    mut v_f_5540_: *mut leanh::LeanObject,
    mut v_as_5541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5542_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_5540_, v_as_5541_);
    leanh::lean_dec_ref(v_as_5541_);
    return v_res_5542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(
    mut v_f_5543_: *mut leanh::LeanObject,
    mut v_sz_5544_: usize,
    mut v_i_5545_: usize,
    mut v_bs_5546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5547_: u8 = 0;
    let mut v_v_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: usize = 0;
    let mut v___x_5554_: usize = 0;
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5561_: u8 = 0;
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut v_node_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5570_: u8 = 0;
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5547_ = lean_usize_dec_lt(v_i_5545_, v_sz_5544_);
                if v___x_5547_ == 0 {
                    leanh::lean_dec(v_f_5543_);
                    return v_bs_5546_;
                } else {
                    v_v_5548_ = lean_array_uget(v_bs_5546_, v_i_5545_);
                    v___x_5549_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5550_ = lean_array_uset(v_bs_5546_, v_i_5545_, v___x_5549_);
                    match leanh::lean_obj_tag(v_v_5548_) {
                        0 => {
                            v_key_5557_ = leanh::lean_ctor_get(v_v_5548_, 0);
                            v_val_5558_ = leanh::lean_ctor_get(v_v_5548_, 1);
                            v_isSharedCheck_5566_ =
                                (!leanh::lean_is_exclusive(v_v_5548_)) as u8;
                            if v_isSharedCheck_5566_ == 0 {
                                v___x_5560_ = v_v_5548_;
                                v_isShared_5561_ = v_isSharedCheck_5566_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_5558_);
                                leanh::lean_inc(v_key_5557_);
                                leanh::lean_dec(v_v_5548_);
                                v___x_5560_ = leanh::lean_box(0);
                                v_isShared_5561_ = v_isSharedCheck_5566_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            v_node_5567_ = leanh::lean_ctor_get(v_v_5548_, 0);
                            v_isSharedCheck_5575_ =
                                (!leanh::lean_is_exclusive(v_v_5548_)) as u8;
                            if v_isSharedCheck_5575_ == 0 {
                                v___x_5569_ = v_v_5548_;
                                v_isShared_5570_ = v_isSharedCheck_5575_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_node_5567_);
                                leanh::lean_dec(v_v_5548_);
                                v___x_5569_ = leanh::lean_box(0);
                                v_isShared_5570_ = v_isSharedCheck_5575_;
                                state = 4;
                                continue;
                            }
                        }
                        _ => {
                            v___x_5576_ = leanh::lean_box(2);
                            v___y_5552_ = v___x_5576_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5553_ = 1usize;
                v___x_5554_ = lean_usize_add(v_i_5545_, v___x_5553_);
                v___x_5555_ = lean_array_uset(v_bs_x27_5550_, v_i_5545_, v___y_5552_);
                v_i_5545_ = v___x_5554_;
                v_bs_5546_ = v___x_5555_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v_f_5543_);
                v___x_5562_ = leanh::lean_apply_1(v_f_5543_, v_val_5558_);
                if v_isShared_5561_ == 0 {
                    leanh::lean_ctor_set(v___x_5560_, 1, v___x_5562_);
                    v___x_5564_ = v___x_5560_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_key_5557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5562_);
                    v___x_5564_ = v_reuseFailAlloc_5565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5552_ = v___x_5564_;
                state = 1;
                continue;
            }
            4 => {
                leanh::lean_inc(v_f_5543_);
                v___x_5571_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_5543_, v_node_5567_);
                if v_isShared_5570_ == 0 {
                    leanh::lean_ctor_set(v___x_5569_, 0, v___x_5571_);
                    v___x_5573_ = v___x_5569_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5574_, 0, v___x_5571_);
                    v___x_5573_ = v_reuseFailAlloc_5574_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5552_ = v___x_5573_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(
    mut v_f_5577_: *mut leanh::LeanObject,
    mut v_n_5578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v_sz_5583_: usize = 0;
    let mut v___x_5584_: usize = 0;
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_ks_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v_val_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_5578_) == 0 {
                    v_es_5579_ = leanh::lean_ctor_get(v_n_5578_, 0);
                    v_isSharedCheck_5589_ = (!leanh::lean_is_exclusive(v_n_5578_)) as u8;
                    if v_isSharedCheck_5589_ == 0 {
                        v___x_5581_ = v_n_5578_;
                        v_isShared_5582_ = v_isSharedCheck_5589_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_5579_);
                        leanh::lean_dec(v_n_5578_);
                        v___x_5581_ = leanh::lean_box(0);
                        v_isShared_5582_ = v_isSharedCheck_5589_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_5590_ = leanh::lean_ctor_get(v_n_5578_, 0);
                    v_vs_5591_ = leanh::lean_ctor_get(v_n_5578_, 1);
                    v_isSharedCheck_5599_ = (!leanh::lean_is_exclusive(v_n_5578_)) as u8;
                    if v_isSharedCheck_5599_ == 0 {
                        v___x_5593_ = v_n_5578_;
                        v_isShared_5594_ = v_isSharedCheck_5599_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5591_);
                        leanh::lean_inc(v_ks_5590_);
                        leanh::lean_dec(v_n_5578_);
                        v___x_5593_ = leanh::lean_box(0);
                        v_isShared_5594_ = v_isSharedCheck_5599_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5583_ = lean_array_size(v_es_5579_);
                v___x_5584_ = 0usize;
                v___x_5585_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_5577_, v_sz_5583_, v___x_5584_, v_es_5579_);
                if v_isShared_5582_ == 0 {
                    leanh::lean_ctor_set(v___x_5581_, 0, v___x_5585_);
                    v___x_5587_ = v___x_5581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5588_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5585_);
                    v___x_5587_ = v_reuseFailAlloc_5588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5587_;
            }
            3 => {
                v_val_5595_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_5577_, v_vs_5591_);
                leanh::lean_dec_ref(v_vs_5591_);
                if v_isShared_5594_ == 0 {
                    leanh::lean_ctor_set(v___x_5593_, 1, v_val_5595_);
                    v___x_5597_ = v___x_5593_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5598_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_ks_5590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5598_, 1, v_val_5595_);
                    v___x_5597_ = v_reuseFailAlloc_5598_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5597_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg___boxed(
    mut v_f_5600_: *mut leanh::LeanObject,
    mut v_sz_5601_: *mut leanh::LeanObject,
    mut v_i_5602_: *mut leanh::LeanObject,
    mut v_bs_5603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5604_: usize = 0;
    let mut v_i_boxed_5605_: usize = 0;
    let mut v_res_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5604_ = leanh::lean_unbox_usize(v_sz_5601_);
    leanh::lean_dec(v_sz_5601_);
    v_i_boxed_5605_ = leanh::lean_unbox_usize(v_i_5602_);
    leanh::lean_dec(v_i_5602_);
    v_res_5606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_5600_, v_sz_boxed_5604_, v_i_boxed_5605_, v_bs_5603_);
    return v_res_5606_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(
    mut v_pm_5607_: *mut leanh::LeanObject,
    mut v_f_5608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5609_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_5609_, 0, v_f_5608_);
    v___x_5610_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v___f_5609_, v_pm_5607_);
    return v___x_5610_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(
    mut v___x_5611_: *mut leanh::LeanObject,
    mut v_sz_5612_: usize,
    mut v_i_5613_: usize,
    mut v_bs_5614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5615_: u8 = 0;
    let mut v_v_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: usize = 0;
    let mut v___x_5622_: usize = 0;
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5615_ = lean_usize_dec_lt(v_i_5613_, v_sz_5612_);
                if v___x_5615_ == 0 {
                    return v_bs_5614_;
                } else {
                    v_v_5616_ = lean_array_uget(v_bs_5614_, v_i_5613_);
                    v___x_5617_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5618_ = lean_array_uset(v_bs_5614_, v_i_5613_, v___x_5617_);
                    if leanh::lean_obj_tag(v_v_5616_) == 0 {
                        v___y_5620_ = v_v_5616_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5625_ = leanh::lean_ctor_get(v_v_5616_, 0);
                        v_isSharedCheck_5633_ = (!leanh::lean_is_exclusive(v_v_5616_)) as u8;
                        if v_isSharedCheck_5633_ == 0 {
                            v___x_5627_ = v_v_5616_;
                            v_isShared_5628_ = v_isSharedCheck_5633_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_5625_);
                            leanh::lean_dec(v_v_5616_);
                            v___x_5627_ = leanh::lean_box(0);
                            v_isShared_5628_ = v_isSharedCheck_5633_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5621_ = 1usize;
                v___x_5622_ = lean_usize_add(v_i_5613_, v___x_5621_);
                v___x_5623_ = lean_array_uset(v_bs_x27_5618_, v_i_5613_, v___y_5620_);
                v_i_5613_ = v___x_5622_;
                v_bs_5614_ = v___x_5623_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5629_ =
                    l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_reorder(v_val_5625_, v___x_5611_);
                if v_isShared_5628_ == 0 {
                    leanh::lean_ctor_set(v___x_5627_, 0, v___x_5629_);
                    v___x_5631_ = v___x_5627_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5632_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5632_, 0, v___x_5629_);
                    v___x_5631_ = v_reuseFailAlloc_5632_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5620_ = v___x_5631_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12___boxed(
    mut v___x_5634_: *mut leanh::LeanObject,
    mut v_sz_5635_: *mut leanh::LeanObject,
    mut v_i_5636_: *mut leanh::LeanObject,
    mut v_bs_5637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5638_: usize = 0;
    let mut v_i_boxed_5639_: usize = 0;
    let mut v_res_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5638_ = leanh::lean_unbox_usize(v_sz_5635_);
    leanh::lean_dec(v_sz_5635_);
    v_i_boxed_5639_ = leanh::lean_unbox_usize(v_i_5636_);
    leanh::lean_dec(v_i_5636_);
    v_res_5640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_5634_, v_sz_boxed_5638_, v_i_boxed_5639_, v_bs_5637_);
    leanh::lean_dec_ref(v___x_5634_);
    return v_res_5640_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(
    mut v___x_5641_: *mut leanh::LeanObject,
    mut v_sz_5642_: usize,
    mut v_i_5643_: usize,
    mut v_bs_5644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5645_: u8 = 0;
    let mut v_v_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: usize = 0;
    let mut v___x_5651_: usize = 0;
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5645_ = lean_usize_dec_lt(v_i_5643_, v_sz_5642_);
                if v___x_5645_ == 0 {
                    return v_bs_5644_;
                } else {
                    v_v_5646_ = lean_array_uget(v_bs_5644_, v_i_5643_);
                    v___x_5647_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5648_ = lean_array_uset(v_bs_5644_, v_i_5643_, v___x_5647_);
                    v___x_5649_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_5641_, v_v_5646_);
                    v___x_5650_ = 1usize;
                    v___x_5651_ = lean_usize_add(v_i_5643_, v___x_5650_);
                    v___x_5652_ = lean_array_uset(v_bs_x27_5648_, v_i_5643_, v___x_5649_);
                    v_i_5643_ = v___x_5651_;
                    v_bs_5644_ = v___x_5652_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(
    mut v___x_5654_: *mut leanh::LeanObject,
    mut v_x_5655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v_sz_5660_: usize = 0;
    let mut v___x_5661_: usize = 0;
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5666_: u8 = 0;
    let mut v_vs_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5670_: u8 = 0;
    let mut v_sz_5671_: usize = 0;
    let mut v___x_5672_: usize = 0;
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5655_) == 0 {
                    v_cs_5656_ = leanh::lean_ctor_get(v_x_5655_, 0);
                    v_isSharedCheck_5666_ = (!leanh::lean_is_exclusive(v_x_5655_)) as u8;
                    if v_isSharedCheck_5666_ == 0 {
                        v___x_5658_ = v_x_5655_;
                        v_isShared_5659_ = v_isSharedCheck_5666_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_5656_);
                        leanh::lean_dec(v_x_5655_);
                        v___x_5658_ = leanh::lean_box(0);
                        v_isShared_5659_ = v_isSharedCheck_5666_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5667_ = leanh::lean_ctor_get(v_x_5655_, 0);
                    v_isSharedCheck_5677_ = (!leanh::lean_is_exclusive(v_x_5655_)) as u8;
                    if v_isSharedCheck_5677_ == 0 {
                        v___x_5669_ = v_x_5655_;
                        v_isShared_5670_ = v_isSharedCheck_5677_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5667_);
                        leanh::lean_dec(v_x_5655_);
                        v___x_5669_ = leanh::lean_box(0);
                        v_isShared_5670_ = v_isSharedCheck_5677_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5660_ = lean_array_size(v_cs_5656_);
                v___x_5661_ = 0usize;
                v___x_5662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_5654_, v_sz_5660_, v___x_5661_, v_cs_5656_);
                if v_isShared_5659_ == 0 {
                    leanh::lean_ctor_set(v___x_5658_, 0, v___x_5662_);
                    v___x_5664_ = v___x_5658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5665_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5665_, 0, v___x_5662_);
                    v___x_5664_ = v_reuseFailAlloc_5665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5664_;
            }
            3 => {
                v_sz_5671_ = lean_array_size(v_vs_5667_);
                v___x_5672_ = 0usize;
                v___x_5673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_5654_, v_sz_5671_, v___x_5672_, v_vs_5667_);
                if v_isShared_5670_ == 0 {
                    leanh::lean_ctor_set(v___x_5669_, 0, v___x_5673_);
                    v___x_5675_ = v___x_5669_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5676_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5673_);
                    v___x_5675_ = v_reuseFailAlloc_5676_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11___boxed(
    mut v___x_5678_: *mut leanh::LeanObject,
    mut v_x_5679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5680_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_5678_, v_x_5679_);
    leanh::lean_dec_ref(v___x_5678_);
    return v_res_5680_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16___boxed(
    mut v___x_5681_: *mut leanh::LeanObject,
    mut v_sz_5682_: *mut leanh::LeanObject,
    mut v_i_5683_: *mut leanh::LeanObject,
    mut v_bs_5684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5685_: usize = 0;
    let mut v_i_boxed_5686_: usize = 0;
    let mut v_res_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5685_ = leanh::lean_unbox_usize(v_sz_5682_);
    leanh::lean_dec(v_sz_5682_);
    v_i_boxed_5686_ = leanh::lean_unbox_usize(v_i_5683_);
    leanh::lean_dec(v_i_5683_);
    v_res_5687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11_spec__16(v___x_5681_, v_sz_boxed_5685_, v_i_boxed_5686_, v_bs_5684_);
    leanh::lean_dec_ref(v___x_5681_);
    return v_res_5687_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(
    mut v___x_5688_: *mut leanh::LeanObject,
    mut v_t_5689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5693_: usize = 0;
    let mut v_tailOff_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5697_: u8 = 0;
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5699_: usize = 0;
    let mut v___x_5700_: usize = 0;
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5690_ = leanh::lean_ctor_get(v_t_5689_, 0);
                v_tail_5691_ = leanh::lean_ctor_get(v_t_5689_, 1);
                v_size_5692_ = leanh::lean_ctor_get(v_t_5689_, 2);
                v_shift_5693_ = leanh::lean_ctor_get_usize(v_t_5689_, 4);
                v_tailOff_5694_ = leanh::lean_ctor_get(v_t_5689_, 3);
                v_isSharedCheck_5705_ = (!leanh::lean_is_exclusive(v_t_5689_)) as u8;
                if v_isSharedCheck_5705_ == 0 {
                    v___x_5696_ = v_t_5689_;
                    v_isShared_5697_ = v_isSharedCheck_5705_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_5694_);
                    leanh::lean_inc(v_size_5692_);
                    leanh::lean_inc(v_tail_5691_);
                    leanh::lean_inc(v_root_5690_);
                    leanh::lean_dec(v_t_5689_);
                    v___x_5696_ = leanh::lean_box(0);
                    v_isShared_5697_ = v_isSharedCheck_5705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5698_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__11(v___x_5688_, v_root_5690_);
                v_sz_5699_ = lean_array_size(v_tail_5691_);
                v___x_5700_ = 0usize;
                v___x_5701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4_spec__12(v___x_5688_, v_sz_5699_, v___x_5700_, v_tail_5691_);
                if v_isShared_5697_ == 0 {
                    leanh::lean_ctor_set(v___x_5696_, 1, v___x_5701_);
                    leanh::lean_ctor_set(v___x_5696_, 0, v___x_5698_);
                    v___x_5703_ = v___x_5696_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5704_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 0, v___x_5698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 1, v___x_5701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 2, v_size_5692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5704_, 3, v_tailOff_5694_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_5704_, 4, v_shift_5693_);
                    v___x_5703_ = v_reuseFailAlloc_5704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4___boxed(
    mut v___x_5706_: *mut leanh::LeanObject,
    mut v_t_5707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5708_ =
        l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(
            v___x_5706_,
            v_t_5707_,
        );
    leanh::lean_dec_ref(v___x_5706_);
    return v_res_5708_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5709_ = leanh::lean_unsigned_to_nat(32);
    v___x_5710_ = lean_mk_empty_array_with_capacity(v___x_5709_);
    v___x_5711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5711_, 0, v___x_5710_);
    return v___x_5711_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5712_: usize = 0;
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5712_ = 5usize;
    v___x_5713_ = leanh::lean_unsigned_to_nat(0);
    v___x_5714_ = leanh::lean_unsigned_to_nat(32);
    v___x_5715_ = lean_mk_empty_array_with_capacity(v___x_5714_);
    v___x_5716_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__0);
    v___x_5717_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5717_, 0, v___x_5716_);
    leanh::lean_ctor_set(v___x_5717_, 1, v___x_5715_);
    leanh::lean_ctor_set(v___x_5717_, 2, v___x_5713_);
    leanh::lean_ctor_set(v___x_5717_, 3, v___x_5713_);
    leanh::lean_ctor_set_usize(v___x_5717_, 4, v___x_5712_);
    return v___x_5717_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(
    mut v_sz_5718_: usize,
    mut v_i_5719_: usize,
    mut v_bs_5720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5721_: u8 = 0;
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: usize = 0;
    let mut v___x_5726_: usize = 0;
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5721_ = lean_usize_dec_lt(v_i_5719_, v_sz_5718_);
                if v___x_5721_ == 0 {
                    return v_bs_5720_;
                } else {
                    v___x_5722_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5723_ = lean_array_uset(v_bs_5720_, v_i_5719_, v___x_5722_);
                    v___x_5724_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___closed__1);
                    v___x_5725_ = 1usize;
                    v___x_5726_ = lean_usize_add(v_i_5719_, v___x_5725_);
                    v___x_5727_ = lean_array_uset(v_bs_x27_5723_, v_i_5719_, v___x_5724_);
                    v_i_5719_ = v___x_5726_;
                    v_bs_5720_ = v___x_5727_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9___boxed(
    mut v_sz_5729_: *mut leanh::LeanObject,
    mut v_i_5730_: *mut leanh::LeanObject,
    mut v_bs_5731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5732_: usize = 0;
    let mut v_i_boxed_5733_: usize = 0;
    let mut v_res_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5732_ = leanh::lean_unbox_usize(v_sz_5729_);
    leanh::lean_dec(v_sz_5729_);
    v_i_boxed_5733_ = leanh::lean_unbox_usize(v_i_5730_);
    leanh::lean_dec(v_i_5730_);
    v_res_5734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_boxed_5732_, v_i_boxed_5733_, v_bs_5731_);
    return v_res_5734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(
    mut v_sz_5735_: usize,
    mut v_i_5736_: usize,
    mut v_bs_5737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5738_: u8 = 0;
    let mut v_v_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: usize = 0;
    let mut v___x_5744_: usize = 0;
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5738_ = lean_usize_dec_lt(v_i_5736_, v_sz_5735_);
                if v___x_5738_ == 0 {
                    return v_bs_5737_;
                } else {
                    v_v_5739_ = lean_array_uget(v_bs_5737_, v_i_5736_);
                    v___x_5740_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5741_ = lean_array_uset(v_bs_5737_, v_i_5736_, v___x_5740_);
                    v___x_5742_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_v_5739_);
                    v___x_5743_ = 1usize;
                    v___x_5744_ = lean_usize_add(v_i_5736_, v___x_5743_);
                    v___x_5745_ = lean_array_uset(v_bs_x27_5741_, v_i_5736_, v___x_5742_);
                    v_i_5736_ = v___x_5744_;
                    v_bs_5737_ = v___x_5745_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(
    mut v_x_5747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5751_: u8 = 0;
    let mut v_sz_5752_: usize = 0;
    let mut v___x_5753_: usize = 0;
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5758_: u8 = 0;
    let mut v_vs_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v_sz_5763_: usize = 0;
    let mut v___x_5764_: usize = 0;
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5747_) == 0 {
                    v_cs_5748_ = leanh::lean_ctor_get(v_x_5747_, 0);
                    v_isSharedCheck_5758_ = (!leanh::lean_is_exclusive(v_x_5747_)) as u8;
                    if v_isSharedCheck_5758_ == 0 {
                        v___x_5750_ = v_x_5747_;
                        v_isShared_5751_ = v_isSharedCheck_5758_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_5748_);
                        leanh::lean_dec(v_x_5747_);
                        v___x_5750_ = leanh::lean_box(0);
                        v_isShared_5751_ = v_isSharedCheck_5758_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5759_ = leanh::lean_ctor_get(v_x_5747_, 0);
                    v_isSharedCheck_5769_ = (!leanh::lean_is_exclusive(v_x_5747_)) as u8;
                    if v_isSharedCheck_5769_ == 0 {
                        v___x_5761_ = v_x_5747_;
                        v_isShared_5762_ = v_isSharedCheck_5769_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5759_);
                        leanh::lean_dec(v_x_5747_);
                        v___x_5761_ = leanh::lean_box(0);
                        v_isShared_5762_ = v_isSharedCheck_5769_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5752_ = lean_array_size(v_cs_5748_);
                v___x_5753_ = 0usize;
                v___x_5754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_5752_, v___x_5753_, v_cs_5748_);
                if v_isShared_5751_ == 0 {
                    leanh::lean_ctor_set(v___x_5750_, 0, v___x_5754_);
                    v___x_5756_ = v___x_5750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5754_);
                    v___x_5756_ = v_reuseFailAlloc_5757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5756_;
            }
            3 => {
                v_sz_5763_ = lean_array_size(v_vs_5759_);
                v___x_5764_ = 0usize;
                v___x_5765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_5763_, v___x_5764_, v_vs_5759_);
                if v_isShared_5762_ == 0 {
                    leanh::lean_ctor_set(v___x_5761_, 0, v___x_5765_);
                    v___x_5767_ = v___x_5761_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5768_, 0, v___x_5765_);
                    v___x_5767_ = v_reuseFailAlloc_5768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12___boxed(
    mut v_sz_5770_: *mut leanh::LeanObject,
    mut v_i_5771_: *mut leanh::LeanObject,
    mut v_bs_5772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5773_: usize = 0;
    let mut v_i_boxed_5774_: usize = 0;
    let mut v_res_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5773_ = leanh::lean_unbox_usize(v_sz_5770_);
    leanh::lean_dec(v_sz_5770_);
    v_i_boxed_5774_ = leanh::lean_unbox_usize(v_i_5771_);
    leanh::lean_dec(v_i_5771_);
    v_res_5775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8_spec__12(v_sz_boxed_5773_, v_i_boxed_5774_, v_bs_5772_);
    return v_res_5775_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(
    mut v_t_5776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5780_: usize = 0;
    let mut v_tailOff_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5784_: u8 = 0;
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5786_: usize = 0;
    let mut v___x_5787_: usize = 0;
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5777_ = leanh::lean_ctor_get(v_t_5776_, 0);
                v_tail_5778_ = leanh::lean_ctor_get(v_t_5776_, 1);
                v_size_5779_ = leanh::lean_ctor_get(v_t_5776_, 2);
                v_shift_5780_ = leanh::lean_ctor_get_usize(v_t_5776_, 4);
                v_tailOff_5781_ = leanh::lean_ctor_get(v_t_5776_, 3);
                v_isSharedCheck_5792_ = (!leanh::lean_is_exclusive(v_t_5776_)) as u8;
                if v_isSharedCheck_5792_ == 0 {
                    v___x_5783_ = v_t_5776_;
                    v_isShared_5784_ = v_isSharedCheck_5792_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_5781_);
                    leanh::lean_inc(v_size_5779_);
                    leanh::lean_inc(v_tail_5778_);
                    leanh::lean_inc(v_root_5777_);
                    leanh::lean_dec(v_t_5776_);
                    v___x_5783_ = leanh::lean_box(0);
                    v_isShared_5784_ = v_isSharedCheck_5792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5785_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__8(v_root_5777_);
                v_sz_5786_ = lean_array_size(v_tail_5778_);
                v___x_5787_ = 0usize;
                v___x_5788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3_spec__9(v_sz_5786_, v___x_5787_, v_tail_5778_);
                if v_isShared_5784_ == 0 {
                    leanh::lean_ctor_set(v___x_5783_, 1, v___x_5788_);
                    leanh::lean_ctor_set(v___x_5783_, 0, v___x_5785_);
                    v___x_5790_ = v___x_5783_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5791_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 0, v___x_5785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 1, v___x_5788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 2, v_size_5779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5791_, 3, v_tailOff_5781_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_5791_, 4, v_shift_5780_);
                    v___x_5790_ = v_reuseFailAlloc_5791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5793_ = leanh::lean_unsigned_to_nat(32);
    v___x_5794_ = lean_mk_empty_array_with_capacity(v___x_5793_);
    v___x_5795_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5795_, 0, v___x_5794_);
    return v___x_5795_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5796_: usize = 0;
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5796_ = 5usize;
    v___x_5797_ = leanh::lean_unsigned_to_nat(0);
    v___x_5798_ = leanh::lean_unsigned_to_nat(32);
    v___x_5799_ = lean_mk_empty_array_with_capacity(v___x_5798_);
    v___x_5800_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__0);
    v___x_5801_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_5801_, 0, v___x_5800_);
    leanh::lean_ctor_set(v___x_5801_, 1, v___x_5799_);
    leanh::lean_ctor_set(v___x_5801_, 2, v___x_5797_);
    leanh::lean_ctor_set(v___x_5801_, 3, v___x_5797_);
    leanh::lean_ctor_set_usize(v___x_5801_, 4, v___x_5796_);
    return v___x_5801_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(
    mut v_sz_5802_: usize,
    mut v_i_5803_: usize,
    mut v_bs_5804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5805_: u8 = 0;
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: usize = 0;
    let mut v___x_5810_: usize = 0;
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5805_ = lean_usize_dec_lt(v_i_5803_, v_sz_5802_);
                if v___x_5805_ == 0 {
                    return v_bs_5804_;
                } else {
                    v___x_5806_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5807_ = lean_array_uset(v_bs_5804_, v_i_5803_, v___x_5806_);
                    v___x_5808_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___closed__1);
                    v___x_5809_ = 1usize;
                    v___x_5810_ = lean_usize_add(v_i_5803_, v___x_5809_);
                    v___x_5811_ = lean_array_uset(v_bs_x27_5807_, v_i_5803_, v___x_5808_);
                    v_i_5803_ = v___x_5810_;
                    v_bs_5804_ = v___x_5811_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6___boxed(
    mut v_sz_5813_: *mut leanh::LeanObject,
    mut v_i_5814_: *mut leanh::LeanObject,
    mut v_bs_5815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5816_: usize = 0;
    let mut v_i_boxed_5817_: usize = 0;
    let mut v_res_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5816_ = leanh::lean_unbox_usize(v_sz_5813_);
    leanh::lean_dec(v_sz_5813_);
    v_i_boxed_5817_ = leanh::lean_unbox_usize(v_i_5814_);
    leanh::lean_dec(v_i_5814_);
    v_res_5818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_boxed_5816_, v_i_boxed_5817_, v_bs_5815_);
    return v_res_5818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(
    mut v_sz_5819_: usize,
    mut v_i_5820_: usize,
    mut v_bs_5821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5822_: u8 = 0;
    let mut v_v_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: usize = 0;
    let mut v___x_5828_: usize = 0;
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5822_ = lean_usize_dec_lt(v_i_5820_, v_sz_5819_);
                if v___x_5822_ == 0 {
                    return v_bs_5821_;
                } else {
                    v_v_5823_ = lean_array_uget(v_bs_5821_, v_i_5820_);
                    v___x_5824_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5825_ = lean_array_uset(v_bs_5821_, v_i_5820_, v___x_5824_);
                    v___x_5826_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_v_5823_);
                    v___x_5827_ = 1usize;
                    v___x_5828_ = lean_usize_add(v_i_5820_, v___x_5827_);
                    v___x_5829_ = lean_array_uset(v_bs_x27_5825_, v_i_5820_, v___x_5826_);
                    v_i_5820_ = v___x_5828_;
                    v_bs_5821_ = v___x_5829_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(
    mut v_x_5831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5835_: u8 = 0;
    let mut v_sz_5836_: usize = 0;
    let mut v___x_5837_: usize = 0;
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5842_: u8 = 0;
    let mut v_vs_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5846_: u8 = 0;
    let mut v_sz_5847_: usize = 0;
    let mut v___x_5848_: usize = 0;
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5831_) == 0 {
                    v_cs_5832_ = leanh::lean_ctor_get(v_x_5831_, 0);
                    v_isSharedCheck_5842_ = (!leanh::lean_is_exclusive(v_x_5831_)) as u8;
                    if v_isSharedCheck_5842_ == 0 {
                        v___x_5834_ = v_x_5831_;
                        v_isShared_5835_ = v_isSharedCheck_5842_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_5832_);
                        leanh::lean_dec(v_x_5831_);
                        v___x_5834_ = leanh::lean_box(0);
                        v_isShared_5835_ = v_isSharedCheck_5842_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5843_ = leanh::lean_ctor_get(v_x_5831_, 0);
                    v_isSharedCheck_5853_ = (!leanh::lean_is_exclusive(v_x_5831_)) as u8;
                    if v_isSharedCheck_5853_ == 0 {
                        v___x_5845_ = v_x_5831_;
                        v_isShared_5846_ = v_isSharedCheck_5853_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5843_);
                        leanh::lean_dec(v_x_5831_);
                        v___x_5845_ = leanh::lean_box(0);
                        v_isShared_5846_ = v_isSharedCheck_5853_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5836_ = lean_array_size(v_cs_5832_);
                v___x_5837_ = 0usize;
                v___x_5838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_5836_, v___x_5837_, v_cs_5832_);
                if v_isShared_5835_ == 0 {
                    leanh::lean_ctor_set(v___x_5834_, 0, v___x_5838_);
                    v___x_5840_ = v___x_5834_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5841_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5841_, 0, v___x_5838_);
                    v___x_5840_ = v_reuseFailAlloc_5841_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5840_;
            }
            3 => {
                v_sz_5847_ = lean_array_size(v_vs_5843_);
                v___x_5848_ = 0usize;
                v___x_5849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_5847_, v___x_5848_, v_vs_5843_);
                if v_isShared_5846_ == 0 {
                    leanh::lean_ctor_set(v___x_5845_, 0, v___x_5849_);
                    v___x_5851_ = v___x_5845_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5852_, 0, v___x_5849_);
                    v___x_5851_ = v_reuseFailAlloc_5852_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5851_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8___boxed(
    mut v_sz_5854_: *mut leanh::LeanObject,
    mut v_i_5855_: *mut leanh::LeanObject,
    mut v_bs_5856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5857_: usize = 0;
    let mut v_i_boxed_5858_: usize = 0;
    let mut v_res_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5857_ = leanh::lean_unbox_usize(v_sz_5854_);
    leanh::lean_dec(v_sz_5854_);
    v_i_boxed_5858_ = leanh::lean_unbox_usize(v_i_5855_);
    leanh::lean_dec(v_i_5855_);
    v_res_5859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5_spec__8(v_sz_boxed_5857_, v_i_boxed_5858_, v_bs_5856_);
    return v_res_5859_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(
    mut v_t_5860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5864_: usize = 0;
    let mut v_tailOff_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5868_: u8 = 0;
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5870_: usize = 0;
    let mut v___x_5871_: usize = 0;
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5861_ = leanh::lean_ctor_get(v_t_5860_, 0);
                v_tail_5862_ = leanh::lean_ctor_get(v_t_5860_, 1);
                v_size_5863_ = leanh::lean_ctor_get(v_t_5860_, 2);
                v_shift_5864_ = leanh::lean_ctor_get_usize(v_t_5860_, 4);
                v_tailOff_5865_ = leanh::lean_ctor_get(v_t_5860_, 3);
                v_isSharedCheck_5876_ = (!leanh::lean_is_exclusive(v_t_5860_)) as u8;
                if v_isSharedCheck_5876_ == 0 {
                    v___x_5867_ = v_t_5860_;
                    v_isShared_5868_ = v_isSharedCheck_5876_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_5865_);
                    leanh::lean_inc(v_size_5863_);
                    leanh::lean_inc(v_tail_5862_);
                    leanh::lean_inc(v_root_5861_);
                    leanh::lean_dec(v_t_5860_);
                    v___x_5867_ = leanh::lean_box(0);
                    v_isShared_5868_ = v_isSharedCheck_5876_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5869_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__5(v_root_5861_);
                v_sz_5870_ = lean_array_size(v_tail_5862_);
                v___x_5871_ = 0usize;
                v___x_5872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2_spec__6(v_sz_5870_, v___x_5871_, v_tail_5862_);
                if v_isShared_5868_ == 0 {
                    leanh::lean_ctor_set(v___x_5867_, 1, v___x_5872_);
                    leanh::lean_ctor_set(v___x_5867_, 0, v___x_5869_);
                    v___x_5874_ = v___x_5867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 0, v___x_5869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 1, v___x_5872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_size_5863_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 3, v_tailOff_5865_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_5875_, 4, v_shift_5864_);
                    v___x_5874_ = v_reuseFailAlloc_5875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(
    mut v_sz_5877_: usize,
    mut v_i_5878_: usize,
    mut v_bs_5879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5880_: u8 = 0;
    let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: usize = 0;
    let mut v___x_5885_: usize = 0;
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5880_ = lean_usize_dec_lt(v_i_5878_, v_sz_5877_);
                if v___x_5880_ == 0 {
                    return v_bs_5879_;
                } else {
                    v___x_5881_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5882_ = lean_array_uset(v_bs_5879_, v_i_5878_, v___x_5881_);
                    v___x_5883_ = leanh::lean_box(1);
                    v___x_5884_ = 1usize;
                    v___x_5885_ = lean_usize_add(v_i_5878_, v___x_5884_);
                    v___x_5886_ = lean_array_uset(v_bs_x27_5882_, v_i_5878_, v___x_5883_);
                    v_i_5878_ = v___x_5885_;
                    v_bs_5879_ = v___x_5886_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16___boxed(
    mut v_sz_5888_: *mut leanh::LeanObject,
    mut v_i_5889_: *mut leanh::LeanObject,
    mut v_bs_5890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5891_: usize = 0;
    let mut v_i_boxed_5892_: usize = 0;
    let mut v_res_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5891_ = leanh::lean_unbox_usize(v_sz_5888_);
    leanh::lean_dec(v_sz_5888_);
    v_i_boxed_5892_ = leanh::lean_unbox_usize(v_i_5889_);
    leanh::lean_dec(v_i_5889_);
    v_res_5893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_boxed_5891_, v_i_boxed_5892_, v_bs_5890_);
    return v_res_5893_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(
    mut v_sz_5894_: usize,
    mut v_i_5895_: usize,
    mut v_bs_5896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5897_: u8 = 0;
    let mut v_v_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: usize = 0;
    let mut v___x_5903_: usize = 0;
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5897_ = lean_usize_dec_lt(v_i_5895_, v_sz_5894_);
                if v___x_5897_ == 0 {
                    return v_bs_5896_;
                } else {
                    v_v_5898_ = lean_array_uget(v_bs_5896_, v_i_5895_);
                    v___x_5899_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5900_ = lean_array_uset(v_bs_5896_, v_i_5895_, v___x_5899_);
                    v___x_5901_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_v_5898_);
                    v___x_5902_ = 1usize;
                    v___x_5903_ = lean_usize_add(v_i_5895_, v___x_5902_);
                    v___x_5904_ = lean_array_uset(v_bs_x27_5900_, v_i_5895_, v___x_5901_);
                    v_i_5895_ = v___x_5903_;
                    v_bs_5896_ = v___x_5904_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(
    mut v_x_5906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5910_: u8 = 0;
    let mut v_sz_5911_: usize = 0;
    let mut v___x_5912_: usize = 0;
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5917_: u8 = 0;
    let mut v_vs_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5921_: u8 = 0;
    let mut v_sz_5922_: usize = 0;
    let mut v___x_5923_: usize = 0;
    let mut v___x_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5906_) == 0 {
                    v_cs_5907_ = leanh::lean_ctor_get(v_x_5906_, 0);
                    v_isSharedCheck_5917_ = (!leanh::lean_is_exclusive(v_x_5906_)) as u8;
                    if v_isSharedCheck_5917_ == 0 {
                        v___x_5909_ = v_x_5906_;
                        v_isShared_5910_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_5907_);
                        leanh::lean_dec(v_x_5906_);
                        v___x_5909_ = leanh::lean_box(0);
                        v_isShared_5910_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_5918_ = leanh::lean_ctor_get(v_x_5906_, 0);
                    v_isSharedCheck_5928_ = (!leanh::lean_is_exclusive(v_x_5906_)) as u8;
                    if v_isSharedCheck_5928_ == 0 {
                        v___x_5920_ = v_x_5906_;
                        v_isShared_5921_ = v_isSharedCheck_5928_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_5918_);
                        leanh::lean_dec(v_x_5906_);
                        v___x_5920_ = leanh::lean_box(0);
                        v_isShared_5921_ = v_isSharedCheck_5928_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_5911_ = lean_array_size(v_cs_5907_);
                v___x_5912_ = 0usize;
                v___x_5913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_5911_, v___x_5912_, v_cs_5907_);
                if v_isShared_5910_ == 0 {
                    leanh::lean_ctor_set(v___x_5909_, 0, v___x_5913_);
                    v___x_5915_ = v___x_5909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v___x_5913_);
                    v___x_5915_ = v_reuseFailAlloc_5916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5915_;
            }
            3 => {
                v_sz_5922_ = lean_array_size(v_vs_5918_);
                v___x_5923_ = 0usize;
                v___x_5924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_5922_, v___x_5923_, v_vs_5918_);
                if v_isShared_5921_ == 0 {
                    leanh::lean_ctor_set(v___x_5920_, 0, v___x_5924_);
                    v___x_5926_ = v___x_5920_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 0, v___x_5924_);
                    v___x_5926_ = v_reuseFailAlloc_5927_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21___boxed(
    mut v_sz_5929_: *mut leanh::LeanObject,
    mut v_i_5930_: *mut leanh::LeanObject,
    mut v_bs_5931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5932_: usize = 0;
    let mut v_i_boxed_5933_: usize = 0;
    let mut v_res_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5932_ = leanh::lean_unbox_usize(v_sz_5929_);
    leanh::lean_dec(v_sz_5929_);
    v_i_boxed_5933_ = leanh::lean_unbox_usize(v_i_5930_);
    leanh::lean_dec(v_i_5930_);
    v_res_5934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15_spec__21(v_sz_boxed_5932_, v_i_boxed_5933_, v_bs_5931_);
    return v_res_5934_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(
    mut v_t_5935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_5939_: usize = 0;
    let mut v_tailOff_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5943_: u8 = 0;
    let mut v___x_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5945_: usize = 0;
    let mut v___x_5946_: usize = 0;
    let mut v___x_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5936_ = leanh::lean_ctor_get(v_t_5935_, 0);
                v_tail_5937_ = leanh::lean_ctor_get(v_t_5935_, 1);
                v_size_5938_ = leanh::lean_ctor_get(v_t_5935_, 2);
                v_shift_5939_ = leanh::lean_ctor_get_usize(v_t_5935_, 4);
                v_tailOff_5940_ = leanh::lean_ctor_get(v_t_5935_, 3);
                v_isSharedCheck_5951_ = (!leanh::lean_is_exclusive(v_t_5935_)) as u8;
                if v_isSharedCheck_5951_ == 0 {
                    v___x_5942_ = v_t_5935_;
                    v_isShared_5943_ = v_isSharedCheck_5951_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_5940_);
                    leanh::lean_inc(v_size_5938_);
                    leanh::lean_inc(v_tail_5937_);
                    leanh::lean_inc(v_root_5936_);
                    leanh::lean_dec(v_t_5935_);
                    v___x_5942_ = leanh::lean_box(0);
                    v_isShared_5943_ = v_isSharedCheck_5951_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5944_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__15(v_root_5936_);
                v_sz_5945_ = lean_array_size(v_tail_5937_);
                v___x_5946_ = 0usize;
                v___x_5947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6_spec__16(v_sz_5945_, v___x_5946_, v_tail_5937_);
                if v_isShared_5943_ == 0 {
                    leanh::lean_ctor_set(v___x_5942_, 1, v___x_5947_);
                    leanh::lean_ctor_set(v___x_5942_, 0, v___x_5944_);
                    v___x_5949_ = v___x_5942_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 0, v___x_5944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 1, v___x_5947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 2, v_size_5938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 3, v_tailOff_5940_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_5950_, 4, v_shift_5939_);
                    v___x_5949_ = v_reuseFailAlloc_5950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(
    mut v___x_5952_: *mut leanh::LeanObject,
    mut v_a_5953_: *mut leanh::LeanObject,
    mut v_a_5954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5960_: u8 = 0;
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5953_) == 0 {
                    v___x_5955_ = l_List_reverse___redArg(v_a_5954_);
                    return v___x_5955_;
                } else {
                    v_head_5956_ = leanh::lean_ctor_get(v_a_5953_, 0);
                    v_tail_5957_ = leanh::lean_ctor_get(v_a_5953_, 1);
                    v_isSharedCheck_5967_ = (!leanh::lean_is_exclusive(v_a_5953_)) as u8;
                    if v_isSharedCheck_5967_ == 0 {
                        v___x_5959_ = v_a_5953_;
                        v_isShared_5960_ = v_isSharedCheck_5967_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5957_);
                        leanh::lean_inc(v_head_5956_);
                        leanh::lean_dec(v_a_5953_);
                        v___x_5959_ = leanh::lean_box(0);
                        v_isShared_5960_ = v_isSharedCheck_5967_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5961_ = leanh::lean_unsigned_to_nat(0);
                v___x_5962_ = lean_array_get_borrowed(v___x_5961_, v___x_5952_, v_head_5956_);
                leanh::lean_dec(v_head_5956_);
                leanh::lean_inc(v___x_5962_);
                if v_isShared_5960_ == 0 {
                    leanh::lean_ctor_set(v___x_5959_, 1, v_a_5954_);
                    leanh::lean_ctor_set(v___x_5959_, 0, v___x_5962_);
                    v___x_5964_ = v___x_5959_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5966_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5962_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5966_, 1, v_a_5954_);
                    v___x_5964_ = v_reuseFailAlloc_5966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5953_ = v_tail_5957_;
                v_a_5954_ = v___x_5964_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5___boxed(
    mut v___x_5968_: *mut leanh::LeanObject,
    mut v_a_5969_: *mut leanh::LeanObject,
    mut v_a_5970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5971_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(
        v___x_5968_,
        v_a_5969_,
        v_a_5970_,
    );
    leanh::lean_dec_ref(v___x_5968_);
    return v_res_5971_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(
    mut v_sz_5972_: usize,
    mut v_i_5973_: usize,
    mut v_bs_5974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5975_: u8 = 0;
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: usize = 0;
    let mut v___x_5980_: usize = 0;
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5975_ = lean_usize_dec_lt(v_i_5973_, v_sz_5972_);
                if v___x_5975_ == 0 {
                    return v_bs_5974_;
                } else {
                    v___x_5976_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5977_ = lean_array_uset(v_bs_5974_, v_i_5973_, v___x_5976_);
                    v___x_5978_ = leanh::lean_box(0);
                    v___x_5979_ = 1usize;
                    v___x_5980_ = lean_usize_add(v_i_5973_, v___x_5979_);
                    v___x_5981_ = lean_array_uset(v_bs_x27_5977_, v_i_5973_, v___x_5978_);
                    v_i_5973_ = v___x_5980_;
                    v_bs_5974_ = v___x_5981_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3___boxed(
    mut v_sz_5983_: *mut leanh::LeanObject,
    mut v_i_5984_: *mut leanh::LeanObject,
    mut v_bs_5985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5986_: usize = 0;
    let mut v_i_boxed_5987_: usize = 0;
    let mut v_res_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5986_ = leanh::lean_unbox_usize(v_sz_5983_);
    leanh::lean_dec(v_sz_5983_);
    v_i_boxed_5987_ = leanh::lean_unbox_usize(v_i_5984_);
    leanh::lean_dec(v_i_5984_);
    v_res_5988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_boxed_5986_, v_i_boxed_5987_, v_bs_5985_);
    return v_res_5988_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(
    mut v_sz_5989_: usize,
    mut v_i_5990_: usize,
    mut v_bs_5991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5992_: u8 = 0;
    let mut v_v_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: usize = 0;
    let mut v___x_5998_: usize = 0;
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5992_ = lean_usize_dec_lt(v_i_5990_, v_sz_5989_);
                if v___x_5992_ == 0 {
                    return v_bs_5991_;
                } else {
                    v_v_5993_ = lean_array_uget(v_bs_5991_, v_i_5990_);
                    v___x_5994_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5995_ = lean_array_uset(v_bs_5991_, v_i_5990_, v___x_5994_);
                    v___x_5996_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_v_5993_);
                    v___x_5997_ = 1usize;
                    v___x_5998_ = lean_usize_add(v_i_5990_, v___x_5997_);
                    v___x_5999_ = lean_array_uset(v_bs_x27_5995_, v_i_5990_, v___x_5996_);
                    v_i_5990_ = v___x_5998_;
                    v_bs_5991_ = v___x_5999_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(
    mut v_x_6001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6005_: u8 = 0;
    let mut v_sz_6006_: usize = 0;
    let mut v___x_6007_: usize = 0;
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6012_: u8 = 0;
    let mut v_vs_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v_sz_6017_: usize = 0;
    let mut v___x_6018_: usize = 0;
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6001_) == 0 {
                    v_cs_6002_ = leanh::lean_ctor_get(v_x_6001_, 0);
                    v_isSharedCheck_6012_ = (!leanh::lean_is_exclusive(v_x_6001_)) as u8;
                    if v_isSharedCheck_6012_ == 0 {
                        v___x_6004_ = v_x_6001_;
                        v_isShared_6005_ = v_isSharedCheck_6012_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_cs_6002_);
                        leanh::lean_dec(v_x_6001_);
                        v___x_6004_ = leanh::lean_box(0);
                        v_isShared_6005_ = v_isSharedCheck_6012_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_vs_6013_ = leanh::lean_ctor_get(v_x_6001_, 0);
                    v_isSharedCheck_6023_ = (!leanh::lean_is_exclusive(v_x_6001_)) as u8;
                    if v_isSharedCheck_6023_ == 0 {
                        v___x_6015_ = v_x_6001_;
                        v_isShared_6016_ = v_isSharedCheck_6023_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_6013_);
                        leanh::lean_dec(v_x_6001_);
                        v___x_6015_ = leanh::lean_box(0);
                        v_isShared_6016_ = v_isSharedCheck_6023_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_6006_ = lean_array_size(v_cs_6002_);
                v___x_6007_ = 0usize;
                v___x_6008_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_6006_, v___x_6007_, v_cs_6002_);
                if v_isShared_6005_ == 0 {
                    leanh::lean_ctor_set(v___x_6004_, 0, v___x_6008_);
                    v___x_6010_ = v___x_6004_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6011_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6011_, 0, v___x_6008_);
                    v___x_6010_ = v_reuseFailAlloc_6011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6010_;
            }
            3 => {
                v_sz_6017_ = lean_array_size(v_vs_6013_);
                v___x_6018_ = 0usize;
                v___x_6019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_6017_, v___x_6018_, v_vs_6013_);
                if v_isShared_6016_ == 0 {
                    leanh::lean_ctor_set(v___x_6015_, 0, v___x_6019_);
                    v___x_6021_ = v___x_6015_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6022_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6019_);
                    v___x_6021_ = v_reuseFailAlloc_6022_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4___boxed(
    mut v_sz_6024_: *mut leanh::LeanObject,
    mut v_i_6025_: *mut leanh::LeanObject,
    mut v_bs_6026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6027_: usize = 0;
    let mut v_i_boxed_6028_: usize = 0;
    let mut v_res_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6027_ = leanh::lean_unbox_usize(v_sz_6024_);
    leanh::lean_dec(v_sz_6024_);
    v_i_boxed_6028_ = leanh::lean_unbox_usize(v_i_6025_);
    leanh::lean_dec(v_i_6025_);
    v_res_6029_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2_spec__4(v_sz_boxed_6027_, v_i_boxed_6028_, v_bs_6026_);
    return v_res_6029_;
}
pub unsafe fn l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(
    mut v_t_6030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shift_6034_: usize = 0;
    let mut v_tailOff_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6038_: u8 = 0;
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6040_: usize = 0;
    let mut v___x_6041_: usize = 0;
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6031_ = leanh::lean_ctor_get(v_t_6030_, 0);
                v_tail_6032_ = leanh::lean_ctor_get(v_t_6030_, 1);
                v_size_6033_ = leanh::lean_ctor_get(v_t_6030_, 2);
                v_shift_6034_ = leanh::lean_ctor_get_usize(v_t_6030_, 4);
                v_tailOff_6035_ = leanh::lean_ctor_get(v_t_6030_, 3);
                v_isSharedCheck_6046_ = (!leanh::lean_is_exclusive(v_t_6030_)) as u8;
                if v_isSharedCheck_6046_ == 0 {
                    v___x_6037_ = v_t_6030_;
                    v_isShared_6038_ = v_isSharedCheck_6046_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_tailOff_6035_);
                    leanh::lean_inc(v_size_6033_);
                    leanh::lean_inc(v_tail_6032_);
                    leanh::lean_inc(v_root_6031_);
                    leanh::lean_dec(v_t_6030_);
                    v___x_6037_ = leanh::lean_box(0);
                    v_isShared_6038_ = v_isSharedCheck_6046_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6039_ = l_Lean_PersistentArray_mapMAux___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__2(v_root_6031_);
                v_sz_6040_ = lean_array_size(v_tail_6032_);
                v___x_6041_ = 0usize;
                v___x_6042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1_spec__3(v_sz_6040_, v___x_6041_, v_tail_6032_);
                if v_isShared_6038_ == 0 {
                    leanh::lean_ctor_set(v___x_6037_, 1, v___x_6042_);
                    leanh::lean_ctor_set(v___x_6037_, 0, v___x_6039_);
                    v___x_6044_ = v___x_6037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6045_ = leanh::lean_alloc_ctor(
                        0,
                        4,
                        (core::mem::size_of::<usize>() * 1) as u32,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6045_, 0, v___x_6039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6045_, 1, v___x_6042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6045_, 2, v_size_6033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6045_, 3, v_tailOff_6035_);
                    leanh::lean_ctor_set_usize(v_reuseFailAlloc_6045_, 4, v_shift_6034_);
                    v___x_6044_ = v_reuseFailAlloc_6045_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(
    mut v_a_6047_: *mut leanh::LeanObject,
    mut v___f_6048_: *mut leanh::LeanObject,
    mut v___x_6049_: *mut leanh::LeanObject,
    mut v_s_6050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natDef_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_6057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_6059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_elimStack_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occurs_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_caseSplits_6064_: u8 = 0;
    let mut v_conflict_x3f_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_divMod_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_6068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_6071_: u8 = 0;
    let mut v_nonlinearOccs_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6075_: u8 = 0;
    let mut v___x_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6094_: u8 = 0;
    let mut v_unused_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_6051_ = leanh::lean_ctor_get(v_s_6050_, 0);
                v_varMap_6052_ = leanh::lean_ctor_get(v_s_6050_, 1);
                v_natToIntMap_6053_ = leanh::lean_ctor_get(v_s_6050_, 4);
                v_natDef_6054_ = leanh::lean_ctor_get(v_s_6050_, 5);
                v_dvds_6055_ = leanh::lean_ctor_get(v_s_6050_, 6);
                v_lowers_6056_ = leanh::lean_ctor_get(v_s_6050_, 7);
                v_uppers_6057_ = leanh::lean_ctor_get(v_s_6050_, 8);
                v_diseqs_6058_ = leanh::lean_ctor_get(v_s_6050_, 9);
                v_elimEqs_6059_ = leanh::lean_ctor_get(v_s_6050_, 10);
                v_elimStack_6060_ = leanh::lean_ctor_get(v_s_6050_, 11);
                v_occurs_6061_ = leanh::lean_ctor_get(v_s_6050_, 12);
                v_assignment_6062_ = leanh::lean_ctor_get(v_s_6050_, 13);
                v_nextCnstrId_6063_ = leanh::lean_ctor_get(v_s_6050_, 14);
                v_caseSplits_6064_ = leanh::lean_ctor_get_uint8(
                    v_s_6050_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 23) as u32,
                );
                v_conflict_x3f_6065_ = leanh::lean_ctor_get(v_s_6050_, 15);
                v_divMod_6066_ = leanh::lean_ctor_get(v_s_6050_, 17);
                v_toIntIds_6067_ = leanh::lean_ctor_get(v_s_6050_, 18);
                v_toIntInfos_6068_ = leanh::lean_ctor_get(v_s_6050_, 19);
                v_toIntTermMap_6069_ = leanh::lean_ctor_get(v_s_6050_, 20);
                v_toIntVarMap_6070_ = leanh::lean_ctor_get(v_s_6050_, 21);
                v_usedCommRing_6071_ = leanh::lean_ctor_get_uint8(
                    v_s_6050_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_6072_ = leanh::lean_ctor_get(v_s_6050_, 22);
                v_isSharedCheck_6094_ = (!leanh::lean_is_exclusive(v_s_6050_)) as u8;
                if v_isSharedCheck_6094_ == 0 {
                    v_unused_6095_ = leanh::lean_ctor_get(v_s_6050_, 16);
                    leanh::lean_dec(v_unused_6095_);
                    v_unused_6096_ = leanh::lean_ctor_get(v_s_6050_, 3);
                    leanh::lean_dec(v_unused_6096_);
                    v_unused_6097_ = leanh::lean_ctor_get(v_s_6050_, 2);
                    leanh::lean_dec(v_unused_6097_);
                    v___x_6074_ = v_s_6050_;
                    v_isShared_6075_ = v_isSharedCheck_6094_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nonlinearOccs_6072_);
                    leanh::lean_inc(v_toIntVarMap_6070_);
                    leanh::lean_inc(v_toIntTermMap_6069_);
                    leanh::lean_inc(v_toIntInfos_6068_);
                    leanh::lean_inc(v_toIntIds_6067_);
                    leanh::lean_inc(v_divMod_6066_);
                    leanh::lean_inc(v_conflict_x3f_6065_);
                    leanh::lean_inc(v_nextCnstrId_6063_);
                    leanh::lean_inc(v_assignment_6062_);
                    leanh::lean_inc(v_occurs_6061_);
                    leanh::lean_inc(v_elimStack_6060_);
                    leanh::lean_inc(v_elimEqs_6059_);
                    leanh::lean_inc(v_diseqs_6058_);
                    leanh::lean_inc(v_uppers_6057_);
                    leanh::lean_inc(v_lowers_6056_);
                    leanh::lean_inc(v_dvds_6055_);
                    leanh::lean_inc(v_natDef_6054_);
                    leanh::lean_inc(v_natToIntMap_6053_);
                    leanh::lean_inc(v_varMap_6052_);
                    leanh::lean_inc(v_vars_6051_);
                    leanh::lean_dec(v_s_6050_);
                    v___x_6074_ = leanh::lean_box(0);
                    v_isShared_6075_ = v_isSharedCheck_6094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6076_ = l_Lean_instInhabitedExpr;
                leanh::lean_inc_ref(v_a_6047_);
                leanh::lean_inc_ref(v_vars_6051_);
                v___x_6077_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(
                    v___x_6076_,
                    v_vars_6051_,
                    v_a_6047_,
                );
                leanh::lean_inc_ref(v___f_6048_);
                leanh::lean_inc_ref(v_varMap_6052_);
                v___x_6078_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_varMap_6052_, v___f_6048_);
                v___x_6079_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_natDef_6054_, v___f_6048_);
                v___x_6080_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__1(v_dvds_6055_);
                v___x_6081_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_lowers_6056_);
                v___x_6082_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__2(v_uppers_6057_);
                v___x_6083_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__3(v_diseqs_6058_);
                v___x_6084_ = leanh::lean_box(0);
                v___x_6085_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVarMap___redArg(
                    v___x_6084_,
                    v_elimEqs_6059_,
                    v_a_6047_,
                );
                v___x_6086_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__4(v___x_6049_, v___x_6085_);
                v___x_6087_ = leanh::lean_box(0);
                v___x_6088_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__5(
                        v___x_6049_,
                        v_elimStack_6060_,
                        v___x_6087_,
                    );
                v___x_6089_ = l_Lean_PersistentArray_mapM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__6(v_occurs_6061_);
                v___x_6090_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderDiseqSplits___closed__1,
                );
                if v_isShared_6075_ == 0 {
                    leanh::lean_ctor_set(v___x_6074_, 16, v___x_6090_);
                    leanh::lean_ctor_set(v___x_6074_, 12, v___x_6089_);
                    leanh::lean_ctor_set(v___x_6074_, 11, v___x_6088_);
                    leanh::lean_ctor_set(v___x_6074_, 10, v___x_6086_);
                    leanh::lean_ctor_set(v___x_6074_, 9, v___x_6083_);
                    leanh::lean_ctor_set(v___x_6074_, 8, v___x_6082_);
                    leanh::lean_ctor_set(v___x_6074_, 7, v___x_6081_);
                    leanh::lean_ctor_set(v___x_6074_, 6, v___x_6080_);
                    leanh::lean_ctor_set(v___x_6074_, 5, v___x_6079_);
                    leanh::lean_ctor_set(v___x_6074_, 3, v_varMap_6052_);
                    leanh::lean_ctor_set(v___x_6074_, 2, v_vars_6051_);
                    leanh::lean_ctor_set(v___x_6074_, 1, v___x_6078_);
                    leanh::lean_ctor_set(v___x_6074_, 0, v___x_6077_);
                    v___x_6092_ = v___x_6074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6093_ = leanh::lean_alloc_ctor(0, 23, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 0, v___x_6077_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 1, v___x_6078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 2, v_vars_6051_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 3, v_varMap_6052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 4, v_natToIntMap_6053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 5, v___x_6079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 6, v___x_6080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 7, v___x_6081_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 8, v___x_6082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 9, v___x_6083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 10, v___x_6086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 11, v___x_6088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 12, v___x_6089_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 13, v_assignment_6062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 14, v_nextCnstrId_6063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 15, v_conflict_x3f_6065_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 16, v___x_6090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 17, v_divMod_6066_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 18, v_toIntIds_6067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 19, v_toIntInfos_6068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 20, v_toIntTermMap_6069_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 21, v_toIntVarMap_6070_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6093_, 22, v_nonlinearOccs_6072_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6093_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 23) as u32,
                        v_caseSplits_6064_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6093_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_6071_,
                    );
                    v___x_6092_ = v_reuseFailAlloc_6093_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed(
    mut v_a_6098_: *mut leanh::LeanObject,
    mut v___f_6099_: *mut leanh::LeanObject,
    mut v___x_6100_: *mut leanh::LeanObject,
    mut v_s_6101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6102_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1(
        v_a_6098_,
        v___f_6099_,
        v___x_6100_,
        v_s_6101_,
    );
    leanh::lean_dec_ref(v___x_6100_);
    return v_res_6102_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(
    mut v_as_6103_: *mut leanh::LeanObject,
    mut v_i_6104_: usize,
    mut v_stop_6105_: usize,
    mut v_b_6106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: usize = 0;
    let mut v___x_6110_: usize = 0;
    let mut v___x_6112_: u8 = 0;
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6112_ = lean_usize_dec_eq(v_i_6104_, v_stop_6105_);
                if v___x_6112_ == 0 {
                    v___x_6113_ = lean_array_uget_borrowed(v_as_6103_, v_i_6104_);
                    if leanh::lean_obj_tag(v___x_6113_) == 0 {
                        v___y_6108_ = v_b_6106_;
                        state = 1;
                        continue;
                    } else {
                        v_val_6114_ = leanh::lean_ctor_get(v___x_6113_, 0);
                        leanh::lean_inc(v_val_6114_);
                        v___x_6115_ = lean_array_push(v_b_6106_, v_val_6114_);
                        v___y_6108_ = v___x_6115_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_6106_;
                }
            }
            1 => {
                v___x_6109_ = 1usize;
                v___x_6110_ = lean_usize_add(v_i_6104_, v___x_6109_);
                v_i_6104_ = v___x_6110_;
                v_b_6106_ = v___y_6108_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19___boxed(
    mut v_as_6116_: *mut leanh::LeanObject,
    mut v_i_6117_: *mut leanh::LeanObject,
    mut v_stop_6118_: *mut leanh::LeanObject,
    mut v_b_6119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6120_: usize = 0;
    let mut v_stop_boxed_6121_: usize = 0;
    let mut v_res_6122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6120_ = leanh::lean_unbox_usize(v_i_6117_);
    leanh::lean_dec(v_i_6117_);
    v_stop_boxed_6121_ = leanh::lean_unbox_usize(v_stop_6118_);
    leanh::lean_dec(v_stop_6118_);
    v_res_6122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_as_6116_, v_i_boxed_6120_, v_stop_boxed_6121_, v_b_6119_);
    leanh::lean_dec_ref(v_as_6116_);
    return v_res_6122_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(
    mut v_x_6123_: *mut leanh::LeanObject,
    mut v_x_6124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6123_) == 0 {
        let mut v_cs_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6128_: u8 = 0;
        v_cs_6125_ = leanh::lean_ctor_get(v_x_6123_, 0);
        v___x_6126_ = leanh::lean_unsigned_to_nat(0);
        v___x_6127_ = lean_array_get_size(v_cs_6125_);
        v___x_6128_ = lean_nat_dec_lt(v___x_6126_, v___x_6127_);
        if v___x_6128_ == 0 {
            return v_x_6124_;
        } else {
            let mut v___x_6129_: u8 = 0;
            v___x_6129_ = lean_nat_dec_le(v___x_6127_, v___x_6127_);
            if v___x_6129_ == 0 {
                if v___x_6128_ == 0 {
                    return v_x_6124_;
                } else {
                    let mut v___x_6130_: usize = 0;
                    let mut v___x_6131_: usize = 0;
                    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6130_ = 0usize;
                    v___x_6131_ = lean_usize_of_nat(v___x_6127_);
                    v___x_6132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_6125_, v___x_6130_, v___x_6131_, v_x_6124_);
                    return v___x_6132_;
                }
            } else {
                let mut v___x_6133_: usize = 0;
                let mut v___x_6134_: usize = 0;
                let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6133_ = 0usize;
                v___x_6134_ = lean_usize_of_nat(v___x_6127_);
                v___x_6135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_6125_, v___x_6133_, v___x_6134_, v_x_6124_);
                return v___x_6135_;
            }
        }
    } else {
        let mut v_vs_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6139_: u8 = 0;
        v_vs_6136_ = leanh::lean_ctor_get(v_x_6123_, 0);
        v___x_6137_ = leanh::lean_unsigned_to_nat(0);
        v___x_6138_ = lean_array_get_size(v_vs_6136_);
        v___x_6139_ = lean_nat_dec_lt(v___x_6137_, v___x_6138_);
        if v___x_6139_ == 0 {
            return v_x_6124_;
        } else {
            let mut v___x_6140_: u8 = 0;
            v___x_6140_ = lean_nat_dec_le(v___x_6138_, v___x_6138_);
            if v___x_6140_ == 0 {
                if v___x_6139_ == 0 {
                    return v_x_6124_;
                } else {
                    let mut v___x_6141_: usize = 0;
                    let mut v___x_6142_: usize = 0;
                    let mut v___x_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6141_ = 0usize;
                    v___x_6142_ = lean_usize_of_nat(v___x_6138_);
                    v___x_6143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_6136_, v___x_6141_, v___x_6142_, v_x_6124_);
                    return v___x_6143_;
                }
            } else {
                let mut v___x_6144_: usize = 0;
                let mut v___x_6145_: usize = 0;
                let mut v___x_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6144_ = 0usize;
                v___x_6145_ = lean_usize_of_nat(v___x_6138_);
                v___x_6146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_6136_, v___x_6144_, v___x_6145_, v_x_6124_);
                return v___x_6146_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(
    mut v_as_6147_: *mut leanh::LeanObject,
    mut v_i_6148_: usize,
    mut v_stop_6149_: usize,
    mut v_b_6150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6151_: u8 = 0;
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: usize = 0;
    let mut v___x_6155_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6151_ = lean_usize_dec_eq(v_i_6148_, v_stop_6149_);
                if v___x_6151_ == 0 {
                    v___x_6152_ = lean_array_uget_borrowed(v_as_6147_, v_i_6148_);
                    v___x_6153_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v___x_6152_, v_b_6150_);
                    v___x_6154_ = 1usize;
                    v___x_6155_ = lean_usize_add(v_i_6148_, v___x_6154_);
                    v_i_6148_ = v___x_6155_;
                    v_b_6150_ = v___x_6153_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6150_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25___boxed(
    mut v_as_6157_: *mut leanh::LeanObject,
    mut v_i_6158_: *mut leanh::LeanObject,
    mut v_stop_6159_: *mut leanh::LeanObject,
    mut v_b_6160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6161_: usize = 0;
    let mut v_stop_boxed_6162_: usize = 0;
    let mut v_res_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6161_ = leanh::lean_unbox_usize(v_i_6158_);
    leanh::lean_dec(v_i_6158_);
    v_stop_boxed_6162_ = leanh::lean_unbox_usize(v_stop_6159_);
    leanh::lean_dec(v_stop_6159_);
    v_res_6163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_as_6157_, v_i_boxed_6161_, v_stop_boxed_6162_, v_b_6160_);
    leanh::lean_dec_ref(v_as_6157_);
    return v_res_6163_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20___boxed(
    mut v_x_6164_: *mut leanh::LeanObject,
    mut v_x_6165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6166_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_x_6164_, v_x_6165_);
    leanh::lean_dec_ref(v_x_6164_);
    return v_res_6166_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6167_ = l_Lean_instInhabitedPersistentArrayNode_default(leanh::lean_box(0));
    return v___x_6167_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(
    mut v_x_6168_: *mut leanh::LeanObject,
    mut v_x_6169_: usize,
    mut v_x_6170_: usize,
    mut v_x_6171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6168_) == 0 {
        let mut v_cs_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6174_: usize = 0;
        let mut v_j_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6177_: usize = 0;
        let mut v___x_6178_: usize = 0;
        let mut v___x_6179_: usize = 0;
        let mut v___x_6180_: usize = 0;
        let mut v___x_6181_: usize = 0;
        let mut v___x_6182_: usize = 0;
        let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6187_: u8 = 0;
        v_cs_6172_ = leanh::lean_ctor_get(v_x_6168_, 0);
        v___x_6173_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
        v___x_6174_ = lean_usize_shift_right(v_x_6169_, v_x_6170_);
        v_j_6175_ = lean_usize_to_nat(v___x_6174_);
        v___x_6176_ = lean_array_get_borrowed(v___x_6173_, v_cs_6172_, v_j_6175_);
        v___x_6177_ = 1usize;
        v___x_6178_ = lean_usize_shift_left(v___x_6177_, v_x_6170_);
        v___x_6179_ = lean_usize_sub(v___x_6178_, v___x_6177_);
        v___x_6180_ = lean_usize_land(v_x_6169_, v___x_6179_);
        v___x_6181_ = 5usize;
        v___x_6182_ = lean_usize_sub(v_x_6170_, v___x_6181_);
        v___x_6183_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v___x_6176_, v___x_6180_, v___x_6182_, v_x_6171_);
        v___x_6184_ = leanh::lean_unsigned_to_nat(1);
        v___x_6185_ = lean_nat_add(v_j_6175_, v___x_6184_);
        leanh::lean_dec(v_j_6175_);
        v___x_6186_ = lean_array_get_size(v_cs_6172_);
        v___x_6187_ = lean_nat_dec_lt(v___x_6185_, v___x_6186_);
        if v___x_6187_ == 0 {
            leanh::lean_dec(v___x_6185_);
            return v___x_6183_;
        } else {
            let mut v___x_6188_: u8 = 0;
            v___x_6188_ = lean_nat_dec_le(v___x_6186_, v___x_6186_);
            if v___x_6188_ == 0 {
                if v___x_6187_ == 0 {
                    leanh::lean_dec(v___x_6185_);
                    return v___x_6183_;
                } else {
                    let mut v___x_6189_: usize = 0;
                    let mut v___x_6190_: usize = 0;
                    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6189_ = lean_usize_of_nat(v___x_6185_);
                    leanh::lean_dec(v___x_6185_);
                    v___x_6190_ = lean_usize_of_nat(v___x_6186_);
                    v___x_6191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_6172_, v___x_6189_, v___x_6190_, v___x_6183_);
                    return v___x_6191_;
                }
            } else {
                let mut v___x_6192_: usize = 0;
                let mut v___x_6193_: usize = 0;
                let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6192_ = lean_usize_of_nat(v___x_6185_);
                leanh::lean_dec(v___x_6185_);
                v___x_6193_ = lean_usize_of_nat(v___x_6186_);
                v___x_6194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18_spec__25(v_cs_6172_, v___x_6192_, v___x_6193_, v___x_6183_);
                return v___x_6194_;
            }
        }
    } else {
        let mut v_vs_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6198_: u8 = 0;
        v_vs_6195_ = leanh::lean_ctor_get(v_x_6168_, 0);
        v___x_6196_ = lean_usize_to_nat(v_x_6169_);
        v___x_6197_ = lean_array_get_size(v_vs_6195_);
        v___x_6198_ = lean_nat_dec_lt(v___x_6196_, v___x_6197_);
        if v___x_6198_ == 0 {
            leanh::lean_dec(v___x_6196_);
            return v_x_6171_;
        } else {
            let mut v___x_6199_: u8 = 0;
            v___x_6199_ = lean_nat_dec_le(v___x_6197_, v___x_6197_);
            if v___x_6199_ == 0 {
                if v___x_6198_ == 0 {
                    leanh::lean_dec(v___x_6196_);
                    return v_x_6171_;
                } else {
                    let mut v___x_6200_: usize = 0;
                    let mut v___x_6201_: usize = 0;
                    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6200_ = lean_usize_of_nat(v___x_6196_);
                    leanh::lean_dec(v___x_6196_);
                    v___x_6201_ = lean_usize_of_nat(v___x_6197_);
                    v___x_6202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_6195_, v___x_6200_, v___x_6201_, v_x_6171_);
                    return v___x_6202_;
                }
            } else {
                let mut v___x_6203_: usize = 0;
                let mut v___x_6204_: usize = 0;
                let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6203_ = lean_usize_of_nat(v___x_6196_);
                leanh::lean_dec(v___x_6196_);
                v___x_6204_ = lean_usize_of_nat(v___x_6197_);
                v___x_6205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_vs_6195_, v___x_6203_, v___x_6204_, v_x_6171_);
                return v___x_6205_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___boxed(
    mut v_x_6206_: *mut leanh::LeanObject,
    mut v_x_6207_: *mut leanh::LeanObject,
    mut v_x_6208_: *mut leanh::LeanObject,
    mut v_x_6209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_92272__boxed_6210_: usize = 0;
    let mut v_x_92273__boxed_6211_: usize = 0;
    let mut v_res_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_92272__boxed_6210_ = leanh::lean_unbox_usize(v_x_6207_);
    leanh::lean_dec(v_x_6207_);
    v_x_92273__boxed_6211_ = leanh::lean_unbox_usize(v_x_6208_);
    leanh::lean_dec(v_x_6208_);
    v_res_6212_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_x_6206_, v_x_92272__boxed_6210_, v_x_92273__boxed_6211_, v_x_6209_);
    leanh::lean_dec_ref(v_x_6206_);
    return v_res_6212_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(
    mut v_t_6213_: *mut leanh::LeanObject,
    mut v_init_6214_: *mut leanh::LeanObject,
    mut v_start_6215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: u8 = 0;
    v___x_6216_ = leanh::lean_unsigned_to_nat(0);
    v___x_6217_ = lean_nat_dec_eq(v_start_6215_, v___x_6216_);
    if v___x_6217_ == 0 {
        let mut v_root_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_6220_: usize = 0;
        let mut v_tailOff_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6222_: u8 = 0;
        v_root_6218_ = leanh::lean_ctor_get(v_t_6213_, 0);
        v_tail_6219_ = leanh::lean_ctor_get(v_t_6213_, 1);
        v_shift_6220_ = leanh::lean_ctor_get_usize(v_t_6213_, 4);
        v_tailOff_6221_ = leanh::lean_ctor_get(v_t_6213_, 3);
        v___x_6222_ = lean_nat_dec_le(v_tailOff_6221_, v_start_6215_);
        if v___x_6222_ == 0 {
            let mut v___x_6223_: usize = 0;
            let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6226_: u8 = 0;
            v___x_6223_ = lean_usize_of_nat(v_start_6215_);
            v___x_6224_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18(v_root_6218_, v___x_6223_, v_shift_6220_, v_init_6214_);
            v___x_6225_ = lean_array_get_size(v_tail_6219_);
            v___x_6226_ = lean_nat_dec_lt(v___x_6216_, v___x_6225_);
            if v___x_6226_ == 0 {
                return v___x_6224_;
            } else {
                let mut v___x_6227_: u8 = 0;
                v___x_6227_ = lean_nat_dec_le(v___x_6225_, v___x_6225_);
                if v___x_6227_ == 0 {
                    if v___x_6226_ == 0 {
                        return v___x_6224_;
                    } else {
                        let mut v___x_6228_: usize = 0;
                        let mut v___x_6229_: usize = 0;
                        let mut v___x_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_6228_ = 0usize;
                        v___x_6229_ = lean_usize_of_nat(v___x_6225_);
                        v___x_6230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_6219_, v___x_6228_, v___x_6229_, v___x_6224_);
                        return v___x_6230_;
                    }
                } else {
                    let mut v___x_6231_: usize = 0;
                    let mut v___x_6232_: usize = 0;
                    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6231_ = 0usize;
                    v___x_6232_ = lean_usize_of_nat(v___x_6225_);
                    v___x_6233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_6219_, v___x_6231_, v___x_6232_, v___x_6224_);
                    return v___x_6233_;
                }
            }
        } else {
            let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6236_: u8 = 0;
            v___x_6234_ = lean_nat_sub(v_start_6215_, v_tailOff_6221_);
            v___x_6235_ = lean_array_get_size(v_tail_6219_);
            v___x_6236_ = lean_nat_dec_lt(v___x_6234_, v___x_6235_);
            if v___x_6236_ == 0 {
                leanh::lean_dec(v___x_6234_);
                return v_init_6214_;
            } else {
                let mut v___x_6237_: u8 = 0;
                v___x_6237_ = lean_nat_dec_le(v___x_6235_, v___x_6235_);
                if v___x_6237_ == 0 {
                    if v___x_6236_ == 0 {
                        leanh::lean_dec(v___x_6234_);
                        return v_init_6214_;
                    } else {
                        let mut v___x_6238_: usize = 0;
                        let mut v___x_6239_: usize = 0;
                        let mut v___x_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_6238_ = lean_usize_of_nat(v___x_6234_);
                        leanh::lean_dec(v___x_6234_);
                        v___x_6239_ = lean_usize_of_nat(v___x_6235_);
                        v___x_6240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_6219_, v___x_6238_, v___x_6239_, v_init_6214_);
                        return v___x_6240_;
                    }
                } else {
                    let mut v___x_6241_: usize = 0;
                    let mut v___x_6242_: usize = 0;
                    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6241_ = lean_usize_of_nat(v___x_6234_);
                    leanh::lean_dec(v___x_6234_);
                    v___x_6242_ = lean_usize_of_nat(v___x_6235_);
                    v___x_6243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_6219_, v___x_6241_, v___x_6242_, v_init_6214_);
                    return v___x_6243_;
                }
            }
        }
    } else {
        let mut v_root_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6248_: u8 = 0;
        v_root_6244_ = leanh::lean_ctor_get(v_t_6213_, 0);
        v_tail_6245_ = leanh::lean_ctor_get(v_t_6213_, 1);
        v___x_6246_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__20(v_root_6244_, v_init_6214_);
        v___x_6247_ = lean_array_get_size(v_tail_6245_);
        v___x_6248_ = lean_nat_dec_lt(v___x_6216_, v___x_6247_);
        if v___x_6248_ == 0 {
            return v___x_6246_;
        } else {
            let mut v___x_6249_: u8 = 0;
            v___x_6249_ = lean_nat_dec_le(v___x_6247_, v___x_6247_);
            if v___x_6249_ == 0 {
                if v___x_6248_ == 0 {
                    return v___x_6246_;
                } else {
                    let mut v___x_6250_: usize = 0;
                    let mut v___x_6251_: usize = 0;
                    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6250_ = 0usize;
                    v___x_6251_ = lean_usize_of_nat(v___x_6247_);
                    v___x_6252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_6245_, v___x_6250_, v___x_6251_, v___x_6246_);
                    return v___x_6252_;
                }
            } else {
                let mut v___x_6253_: usize = 0;
                let mut v___x_6254_: usize = 0;
                let mut v___x_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6253_ = 0usize;
                v___x_6254_ = lean_usize_of_nat(v___x_6247_);
                v___x_6255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__19(v_tail_6245_, v___x_6253_, v___x_6254_, v___x_6246_);
                return v___x_6255_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7___boxed(
    mut v_t_6256_: *mut leanh::LeanObject,
    mut v_init_6257_: *mut leanh::LeanObject,
    mut v_start_6258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6259_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(
            v_t_6256_,
            v_init_6257_,
            v_start_6258_,
        );
    leanh::lean_dec(v_start_6258_);
    leanh::lean_dec_ref(v_t_6256_);
    return v_res_6259_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(
    mut v_as_6260_: *mut leanh::LeanObject,
    mut v_i_6261_: usize,
    mut v_stop_6262_: usize,
    mut v_b_6263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6264_: u8 = 0;
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: usize = 0;
    let mut v___x_6269_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6264_ = lean_usize_dec_eq(v_i_6261_, v_stop_6262_);
                if v___x_6264_ == 0 {
                    v___x_6265_ = lean_array_uget_borrowed(v_as_6260_, v_i_6261_);
                    v___x_6266_ = l_Lean_PersistentArray_toArray___redArg(v___x_6265_);
                    v___x_6267_ = l_Array_append___redArg(v_b_6263_, v___x_6266_);
                    leanh::lean_dec_ref(v___x_6266_);
                    v___x_6268_ = 1usize;
                    v___x_6269_ = lean_usize_add(v_i_6261_, v___x_6268_);
                    v_i_6261_ = v___x_6269_;
                    v_b_6263_ = v___x_6267_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6263_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23___boxed(
    mut v_as_6271_: *mut leanh::LeanObject,
    mut v_i_6272_: *mut leanh::LeanObject,
    mut v_stop_6273_: *mut leanh::LeanObject,
    mut v_b_6274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6275_: usize = 0;
    let mut v_stop_boxed_6276_: usize = 0;
    let mut v_res_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6275_ = leanh::lean_unbox_usize(v_i_6272_);
    leanh::lean_dec(v_i_6272_);
    v_stop_boxed_6276_ = leanh::lean_unbox_usize(v_stop_6273_);
    leanh::lean_dec(v_stop_6273_);
    v_res_6277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_as_6271_, v_i_boxed_6275_, v_stop_boxed_6276_, v_b_6274_);
    leanh::lean_dec_ref(v_as_6271_);
    return v_res_6277_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(
    mut v_x_6278_: *mut leanh::LeanObject,
    mut v_x_6279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6278_) == 0 {
        let mut v_cs_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6283_: u8 = 0;
        v_cs_6280_ = leanh::lean_ctor_get(v_x_6278_, 0);
        v___x_6281_ = leanh::lean_unsigned_to_nat(0);
        v___x_6282_ = lean_array_get_size(v_cs_6280_);
        v___x_6283_ = lean_nat_dec_lt(v___x_6281_, v___x_6282_);
        if v___x_6283_ == 0 {
            return v_x_6279_;
        } else {
            let mut v___x_6284_: u8 = 0;
            v___x_6284_ = lean_nat_dec_le(v___x_6282_, v___x_6282_);
            if v___x_6284_ == 0 {
                if v___x_6283_ == 0 {
                    return v_x_6279_;
                } else {
                    let mut v___x_6285_: usize = 0;
                    let mut v___x_6286_: usize = 0;
                    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6285_ = 0usize;
                    v___x_6286_ = lean_usize_of_nat(v___x_6282_);
                    v___x_6287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_6280_, v___x_6285_, v___x_6286_, v_x_6279_);
                    return v___x_6287_;
                }
            } else {
                let mut v___x_6288_: usize = 0;
                let mut v___x_6289_: usize = 0;
                let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6288_ = 0usize;
                v___x_6289_ = lean_usize_of_nat(v___x_6282_);
                v___x_6290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_6280_, v___x_6288_, v___x_6289_, v_x_6279_);
                return v___x_6290_;
            }
        }
    } else {
        let mut v_vs_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6294_: u8 = 0;
        v_vs_6291_ = leanh::lean_ctor_get(v_x_6278_, 0);
        v___x_6292_ = leanh::lean_unsigned_to_nat(0);
        v___x_6293_ = lean_array_get_size(v_vs_6291_);
        v___x_6294_ = lean_nat_dec_lt(v___x_6292_, v___x_6293_);
        if v___x_6294_ == 0 {
            return v_x_6279_;
        } else {
            let mut v___x_6295_: u8 = 0;
            v___x_6295_ = lean_nat_dec_le(v___x_6293_, v___x_6293_);
            if v___x_6295_ == 0 {
                if v___x_6294_ == 0 {
                    return v_x_6279_;
                } else {
                    let mut v___x_6296_: usize = 0;
                    let mut v___x_6297_: usize = 0;
                    let mut v___x_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6296_ = 0usize;
                    v___x_6297_ = lean_usize_of_nat(v___x_6293_);
                    v___x_6298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_6291_, v___x_6296_, v___x_6297_, v_x_6279_);
                    return v___x_6298_;
                }
            } else {
                let mut v___x_6299_: usize = 0;
                let mut v___x_6300_: usize = 0;
                let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6299_ = 0usize;
                v___x_6300_ = lean_usize_of_nat(v___x_6293_);
                v___x_6301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_6291_, v___x_6299_, v___x_6300_, v_x_6279_);
                return v___x_6301_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(
    mut v_as_6302_: *mut leanh::LeanObject,
    mut v_i_6303_: usize,
    mut v_stop_6304_: usize,
    mut v_b_6305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6306_: u8 = 0;
    let mut v___x_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: usize = 0;
    let mut v___x_6310_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6306_ = lean_usize_dec_eq(v_i_6303_, v_stop_6304_);
                if v___x_6306_ == 0 {
                    v___x_6307_ = lean_array_uget_borrowed(v_as_6302_, v_i_6303_);
                    v___x_6308_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v___x_6307_, v_b_6305_);
                    v___x_6309_ = 1usize;
                    v___x_6310_ = lean_usize_add(v_i_6303_, v___x_6309_);
                    v_i_6303_ = v___x_6310_;
                    v_b_6305_ = v___x_6308_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6305_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30___boxed(
    mut v_as_6312_: *mut leanh::LeanObject,
    mut v_i_6313_: *mut leanh::LeanObject,
    mut v_stop_6314_: *mut leanh::LeanObject,
    mut v_b_6315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6316_: usize = 0;
    let mut v_stop_boxed_6317_: usize = 0;
    let mut v_res_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6316_ = leanh::lean_unbox_usize(v_i_6313_);
    leanh::lean_dec(v_i_6313_);
    v_stop_boxed_6317_ = leanh::lean_unbox_usize(v_stop_6314_);
    leanh::lean_dec(v_stop_6314_);
    v_res_6318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_as_6312_, v_i_boxed_6316_, v_stop_boxed_6317_, v_b_6315_);
    leanh::lean_dec_ref(v_as_6312_);
    return v_res_6318_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24___boxed(
    mut v_x_6319_: *mut leanh::LeanObject,
    mut v_x_6320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6321_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_x_6319_, v_x_6320_);
    leanh::lean_dec_ref(v_x_6319_);
    return v_res_6321_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(
    mut v_x_6322_: *mut leanh::LeanObject,
    mut v_x_6323_: usize,
    mut v_x_6324_: usize,
    mut v_x_6325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6322_) == 0 {
        let mut v_cs_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6328_: usize = 0;
        let mut v_j_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6331_: usize = 0;
        let mut v___x_6332_: usize = 0;
        let mut v___x_6333_: usize = 0;
        let mut v___x_6334_: usize = 0;
        let mut v___x_6335_: usize = 0;
        let mut v___x_6336_: usize = 0;
        let mut v___x_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6341_: u8 = 0;
        v_cs_6326_ = leanh::lean_ctor_get(v_x_6322_, 0);
        v___x_6327_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
        v___x_6328_ = lean_usize_shift_right(v_x_6323_, v_x_6324_);
        v_j_6329_ = lean_usize_to_nat(v___x_6328_);
        v___x_6330_ = lean_array_get_borrowed(v___x_6327_, v_cs_6326_, v_j_6329_);
        v___x_6331_ = 1usize;
        v___x_6332_ = lean_usize_shift_left(v___x_6331_, v_x_6324_);
        v___x_6333_ = lean_usize_sub(v___x_6332_, v___x_6331_);
        v___x_6334_ = lean_usize_land(v_x_6323_, v___x_6333_);
        v___x_6335_ = 5usize;
        v___x_6336_ = lean_usize_sub(v_x_6324_, v___x_6335_);
        v___x_6337_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v___x_6330_, v___x_6334_, v___x_6336_, v_x_6325_);
        v___x_6338_ = leanh::lean_unsigned_to_nat(1);
        v___x_6339_ = lean_nat_add(v_j_6329_, v___x_6338_);
        leanh::lean_dec(v_j_6329_);
        v___x_6340_ = lean_array_get_size(v_cs_6326_);
        v___x_6341_ = lean_nat_dec_lt(v___x_6339_, v___x_6340_);
        if v___x_6341_ == 0 {
            leanh::lean_dec(v___x_6339_);
            return v___x_6337_;
        } else {
            let mut v___x_6342_: u8 = 0;
            v___x_6342_ = lean_nat_dec_le(v___x_6340_, v___x_6340_);
            if v___x_6342_ == 0 {
                if v___x_6341_ == 0 {
                    leanh::lean_dec(v___x_6339_);
                    return v___x_6337_;
                } else {
                    let mut v___x_6343_: usize = 0;
                    let mut v___x_6344_: usize = 0;
                    let mut v___x_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6343_ = lean_usize_of_nat(v___x_6339_);
                    leanh::lean_dec(v___x_6339_);
                    v___x_6344_ = lean_usize_of_nat(v___x_6340_);
                    v___x_6345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_6326_, v___x_6343_, v___x_6344_, v___x_6337_);
                    return v___x_6345_;
                }
            } else {
                let mut v___x_6346_: usize = 0;
                let mut v___x_6347_: usize = 0;
                let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6346_ = lean_usize_of_nat(v___x_6339_);
                leanh::lean_dec(v___x_6339_);
                v___x_6347_ = lean_usize_of_nat(v___x_6340_);
                v___x_6348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22_spec__30(v_cs_6326_, v___x_6346_, v___x_6347_, v___x_6337_);
                return v___x_6348_;
            }
        }
    } else {
        let mut v_vs_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6352_: u8 = 0;
        v_vs_6349_ = leanh::lean_ctor_get(v_x_6322_, 0);
        v___x_6350_ = lean_usize_to_nat(v_x_6323_);
        v___x_6351_ = lean_array_get_size(v_vs_6349_);
        v___x_6352_ = lean_nat_dec_lt(v___x_6350_, v___x_6351_);
        if v___x_6352_ == 0 {
            leanh::lean_dec(v___x_6350_);
            return v_x_6325_;
        } else {
            let mut v___x_6353_: u8 = 0;
            v___x_6353_ = lean_nat_dec_le(v___x_6351_, v___x_6351_);
            if v___x_6353_ == 0 {
                if v___x_6352_ == 0 {
                    leanh::lean_dec(v___x_6350_);
                    return v_x_6325_;
                } else {
                    let mut v___x_6354_: usize = 0;
                    let mut v___x_6355_: usize = 0;
                    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6354_ = lean_usize_of_nat(v___x_6350_);
                    leanh::lean_dec(v___x_6350_);
                    v___x_6355_ = lean_usize_of_nat(v___x_6351_);
                    v___x_6356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_6349_, v___x_6354_, v___x_6355_, v_x_6325_);
                    return v___x_6356_;
                }
            } else {
                let mut v___x_6357_: usize = 0;
                let mut v___x_6358_: usize = 0;
                let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6357_ = lean_usize_of_nat(v___x_6350_);
                leanh::lean_dec(v___x_6350_);
                v___x_6358_ = lean_usize_of_nat(v___x_6351_);
                v___x_6359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_vs_6349_, v___x_6357_, v___x_6358_, v_x_6325_);
                return v___x_6359_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22___boxed(
    mut v_x_6360_: *mut leanh::LeanObject,
    mut v_x_6361_: *mut leanh::LeanObject,
    mut v_x_6362_: *mut leanh::LeanObject,
    mut v_x_6363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_92496__boxed_6364_: usize = 0;
    let mut v_x_92497__boxed_6365_: usize = 0;
    let mut v_res_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_92496__boxed_6364_ = leanh::lean_unbox_usize(v_x_6361_);
    leanh::lean_dec(v_x_6361_);
    v_x_92497__boxed_6365_ = leanh::lean_unbox_usize(v_x_6362_);
    leanh::lean_dec(v_x_6362_);
    v_res_6366_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_x_6360_, v_x_92496__boxed_6364_, v_x_92497__boxed_6365_, v_x_6363_);
    leanh::lean_dec_ref(v_x_6360_);
    return v_res_6366_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(
    mut v_t_6367_: *mut leanh::LeanObject,
    mut v_init_6368_: *mut leanh::LeanObject,
    mut v_start_6369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: u8 = 0;
    v___x_6370_ = leanh::lean_unsigned_to_nat(0);
    v___x_6371_ = lean_nat_dec_eq(v_start_6369_, v___x_6370_);
    if v___x_6371_ == 0 {
        let mut v_root_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_6374_: usize = 0;
        let mut v_tailOff_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6376_: u8 = 0;
        v_root_6372_ = leanh::lean_ctor_get(v_t_6367_, 0);
        v_tail_6373_ = leanh::lean_ctor_get(v_t_6367_, 1);
        v_shift_6374_ = leanh::lean_ctor_get_usize(v_t_6367_, 4);
        v_tailOff_6375_ = leanh::lean_ctor_get(v_t_6367_, 3);
        v___x_6376_ = lean_nat_dec_le(v_tailOff_6375_, v_start_6369_);
        if v___x_6376_ == 0 {
            let mut v___x_6377_: usize = 0;
            let mut v___x_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6380_: u8 = 0;
            v___x_6377_ = lean_usize_of_nat(v_start_6369_);
            v___x_6378_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__22(v_root_6372_, v___x_6377_, v_shift_6374_, v_init_6368_);
            v___x_6379_ = lean_array_get_size(v_tail_6373_);
            v___x_6380_ = lean_nat_dec_lt(v___x_6370_, v___x_6379_);
            if v___x_6380_ == 0 {
                return v___x_6378_;
            } else {
                let mut v___x_6381_: u8 = 0;
                v___x_6381_ = lean_nat_dec_le(v___x_6379_, v___x_6379_);
                if v___x_6381_ == 0 {
                    if v___x_6380_ == 0 {
                        return v___x_6378_;
                    } else {
                        let mut v___x_6382_: usize = 0;
                        let mut v___x_6383_: usize = 0;
                        let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_6382_ = 0usize;
                        v___x_6383_ = lean_usize_of_nat(v___x_6379_);
                        v___x_6384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_6373_, v___x_6382_, v___x_6383_, v___x_6378_);
                        return v___x_6384_;
                    }
                } else {
                    let mut v___x_6385_: usize = 0;
                    let mut v___x_6386_: usize = 0;
                    let mut v___x_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6385_ = 0usize;
                    v___x_6386_ = lean_usize_of_nat(v___x_6379_);
                    v___x_6387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_6373_, v___x_6385_, v___x_6386_, v___x_6378_);
                    return v___x_6387_;
                }
            }
        } else {
            let mut v___x_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6390_: u8 = 0;
            v___x_6388_ = lean_nat_sub(v_start_6369_, v_tailOff_6375_);
            v___x_6389_ = lean_array_get_size(v_tail_6373_);
            v___x_6390_ = lean_nat_dec_lt(v___x_6388_, v___x_6389_);
            if v___x_6390_ == 0 {
                leanh::lean_dec(v___x_6388_);
                return v_init_6368_;
            } else {
                let mut v___x_6391_: u8 = 0;
                v___x_6391_ = lean_nat_dec_le(v___x_6389_, v___x_6389_);
                if v___x_6391_ == 0 {
                    if v___x_6390_ == 0 {
                        leanh::lean_dec(v___x_6388_);
                        return v_init_6368_;
                    } else {
                        let mut v___x_6392_: usize = 0;
                        let mut v___x_6393_: usize = 0;
                        let mut v___x_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_6392_ = lean_usize_of_nat(v___x_6388_);
                        leanh::lean_dec(v___x_6388_);
                        v___x_6393_ = lean_usize_of_nat(v___x_6389_);
                        v___x_6394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_6373_, v___x_6392_, v___x_6393_, v_init_6368_);
                        return v___x_6394_;
                    }
                } else {
                    let mut v___x_6395_: usize = 0;
                    let mut v___x_6396_: usize = 0;
                    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6395_ = lean_usize_of_nat(v___x_6388_);
                    leanh::lean_dec(v___x_6388_);
                    v___x_6396_ = lean_usize_of_nat(v___x_6389_);
                    v___x_6397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_6373_, v___x_6395_, v___x_6396_, v_init_6368_);
                    return v___x_6397_;
                }
            }
        }
    } else {
        let mut v_root_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6402_: u8 = 0;
        v_root_6398_ = leanh::lean_ctor_get(v_t_6367_, 0);
        v_tail_6399_ = leanh::lean_ctor_get(v_t_6367_, 1);
        v___x_6400_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__24(v_root_6398_, v_init_6368_);
        v___x_6401_ = lean_array_get_size(v_tail_6399_);
        v___x_6402_ = lean_nat_dec_lt(v___x_6370_, v___x_6401_);
        if v___x_6402_ == 0 {
            return v___x_6400_;
        } else {
            let mut v___x_6403_: u8 = 0;
            v___x_6403_ = lean_nat_dec_le(v___x_6401_, v___x_6401_);
            if v___x_6403_ == 0 {
                if v___x_6402_ == 0 {
                    return v___x_6400_;
                } else {
                    let mut v___x_6404_: usize = 0;
                    let mut v___x_6405_: usize = 0;
                    let mut v___x_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6404_ = 0usize;
                    v___x_6405_ = lean_usize_of_nat(v___x_6401_);
                    v___x_6406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_6399_, v___x_6404_, v___x_6405_, v___x_6400_);
                    return v___x_6406_;
                }
            } else {
                let mut v___x_6407_: usize = 0;
                let mut v___x_6408_: usize = 0;
                let mut v___x_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6407_ = 0usize;
                v___x_6408_ = lean_usize_of_nat(v___x_6401_);
                v___x_6409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8_spec__23(v_tail_6399_, v___x_6407_, v___x_6408_, v___x_6400_);
                return v___x_6409_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8___boxed(
    mut v_t_6410_: *mut leanh::LeanObject,
    mut v_init_6411_: *mut leanh::LeanObject,
    mut v_start_6412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6413_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(
            v_t_6410_,
            v_init_6411_,
            v_start_6412_,
        );
    leanh::lean_dec(v_start_6412_);
    leanh::lean_dec_ref(v_t_6410_);
    return v_res_6413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(
    mut v___x_6414_: *mut leanh::LeanObject,
    mut v_sz_6415_: usize,
    mut v_i_6416_: usize,
    mut v_bs_6417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6418_: u8 = 0;
    let mut v_v_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: usize = 0;
    let mut v___x_6424_: usize = 0;
    let mut v___x_6425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6418_ = lean_usize_dec_lt(v_i_6416_, v_sz_6415_);
                if v___x_6418_ == 0 {
                    return v_bs_6417_;
                } else {
                    v_v_6419_ = lean_array_uget(v_bs_6417_, v_i_6416_);
                    v___x_6420_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6421_ = lean_array_uset(v_bs_6417_, v_i_6416_, v___x_6420_);
                    v___x_6422_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_reorder(v_v_6419_, v___x_6414_);
                    v___x_6423_ = 1usize;
                    v___x_6424_ = lean_usize_add(v_i_6416_, v___x_6423_);
                    v___x_6425_ = lean_array_uset(v_bs_x27_6421_, v_i_6416_, v___x_6422_);
                    v_i_6416_ = v___x_6424_;
                    v_bs_6417_ = v___x_6425_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10___boxed(
    mut v___x_6427_: *mut leanh::LeanObject,
    mut v_sz_6428_: *mut leanh::LeanObject,
    mut v_i_6429_: *mut leanh::LeanObject,
    mut v_bs_6430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6431_: usize = 0;
    let mut v_i_boxed_6432_: usize = 0;
    let mut v_res_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6431_ = leanh::lean_unbox_usize(v_sz_6428_);
    leanh::lean_dec(v_sz_6428_);
    v_i_boxed_6432_ = leanh::lean_unbox_usize(v_i_6429_);
    leanh::lean_dec(v_i_6429_);
    v_res_6433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_6427_, v_sz_boxed_6431_, v_i_boxed_6432_, v_bs_6430_);
    leanh::lean_dec_ref(v___x_6427_);
    return v_res_6433_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(
    mut v___x_6434_: *mut leanh::LeanObject,
    mut v_sz_6435_: usize,
    mut v_i_6436_: usize,
    mut v_bs_6437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6438_: u8 = 0;
    let mut v_v_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: usize = 0;
    let mut v___x_6444_: usize = 0;
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6438_ = lean_usize_dec_lt(v_i_6436_, v_sz_6435_);
                if v___x_6438_ == 0 {
                    return v_bs_6437_;
                } else {
                    v_v_6439_ = lean_array_uget(v_bs_6437_, v_i_6436_);
                    v___x_6440_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6441_ = lean_array_uset(v_bs_6437_, v_i_6436_, v___x_6440_);
                    v___x_6442_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_reorder(v_v_6439_, v___x_6434_);
                    v___x_6443_ = 1usize;
                    v___x_6444_ = lean_usize_add(v_i_6436_, v___x_6443_);
                    v___x_6445_ = lean_array_uset(v_bs_x27_6441_, v_i_6436_, v___x_6442_);
                    v_i_6436_ = v___x_6444_;
                    v_bs_6437_ = v___x_6445_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14___boxed(
    mut v___x_6447_: *mut leanh::LeanObject,
    mut v_sz_6448_: *mut leanh::LeanObject,
    mut v_i_6449_: *mut leanh::LeanObject,
    mut v_bs_6450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6451_: usize = 0;
    let mut v_i_boxed_6452_: usize = 0;
    let mut v_res_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6451_ = leanh::lean_unbox_usize(v_sz_6448_);
    leanh::lean_dec(v_sz_6448_);
    v_i_boxed_6452_ = leanh::lean_unbox_usize(v_i_6449_);
    leanh::lean_dec(v_i_6449_);
    v_res_6453_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_6447_, v_sz_boxed_6451_, v_i_boxed_6452_, v_bs_6450_);
    leanh::lean_dec_ref(v___x_6447_);
    return v_res_6453_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(
    mut v_msgData_6454_: *mut leanh::LeanObject,
    mut v___y_6455_: *mut leanh::LeanObject,
    mut v___y_6456_: *mut leanh::LeanObject,
    mut v___y_6457_: *mut leanh::LeanObject,
    mut v___y_6458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6460_ = lean_st_ref_get(v___y_6458_);
    v_env_6461_ = leanh::lean_ctor_get(v___x_6460_, 0);
    leanh::lean_inc_ref(v_env_6461_);
    leanh::lean_dec(v___x_6460_);
    v___x_6462_ = lean_st_ref_get(v___y_6456_);
    v_mctx_6463_ = leanh::lean_ctor_get(v___x_6462_, 0);
    leanh::lean_inc_ref(v_mctx_6463_);
    leanh::lean_dec(v___x_6462_);
    v_lctx_6464_ = leanh::lean_ctor_get(v___y_6455_, 2);
    v_options_6465_ = leanh::lean_ctor_get(v___y_6457_, 2);
    leanh::lean_inc_ref(v_options_6465_);
    leanh::lean_inc_ref(v_lctx_6464_);
    v___x_6466_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6466_, 0, v_env_6461_);
    leanh::lean_ctor_set(v___x_6466_, 1, v_mctx_6463_);
    leanh::lean_ctor_set(v___x_6466_, 2, v_lctx_6464_);
    leanh::lean_ctor_set(v___x_6466_, 3, v_options_6465_);
    v___x_6467_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6467_, 0, v___x_6466_);
    leanh::lean_ctor_set(v___x_6467_, 1, v_msgData_6454_);
    v___x_6468_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6468_, 0, v___x_6467_);
    return v___x_6468_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37___boxed(
    mut v_msgData_6469_: *mut leanh::LeanObject,
    mut v___y_6470_: *mut leanh::LeanObject,
    mut v___y_6471_: *mut leanh::LeanObject,
    mut v___y_6472_: *mut leanh::LeanObject,
    mut v___y_6473_: *mut leanh::LeanObject,
    mut v___y_6474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6475_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msgData_6469_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_);
    leanh::lean_dec(v___y_6473_);
    leanh::lean_dec_ref(v___y_6472_);
    leanh::lean_dec(v___y_6471_);
    leanh::lean_dec_ref(v___y_6470_);
    return v_res_6475_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0()
-> f64 {
    let mut v___x_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: f64 = 0.0;
    v___x_6476_ = leanh::lean_unsigned_to_nat(0);
    v___x_6477_ = lean_float_of_nat(v___x_6476_);
    return v___x_6477_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(
    mut v_cls_6481_: *mut leanh::LeanObject,
    mut v_msg_6482_: *mut leanh::LeanObject,
    mut v___y_6483_: *mut leanh::LeanObject,
    mut v___y_6484_: *mut leanh::LeanObject,
    mut v___y_6485_: *mut leanh::LeanObject,
    mut v___y_6486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6493_: u8 = 0;
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6506_: u8 = 0;
    let mut v_tid_6507_: u64 = 0;
    let mut v_traces_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6511_: u8 = 0;
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: f64 = 0.0;
    let mut v___x_6514_: u8 = 0;
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6532_: u8 = 0;
    let mut v_isSharedCheck_6533_: u8 = 0;
    let mut v_isSharedCheck_6534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6488_ = leanh::lean_ctor_get(v___y_6485_, 5);
                v___x_6489_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17_spec__37(v_msg_6482_, v___y_6483_, v___y_6484_, v___y_6485_, v___y_6486_);
                v_a_6490_ = leanh::lean_ctor_get(v___x_6489_, 0);
                v_isSharedCheck_6534_ = (!leanh::lean_is_exclusive(v___x_6489_)) as u8;
                if v_isSharedCheck_6534_ == 0 {
                    v___x_6492_ = v___x_6489_;
                    v_isShared_6493_ = v_isSharedCheck_6534_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6490_);
                    leanh::lean_dec(v___x_6489_);
                    v___x_6492_ = leanh::lean_box(0);
                    v_isShared_6493_ = v_isSharedCheck_6534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6494_ = lean_st_ref_take(v___y_6486_);
                v_traceState_6495_ = leanh::lean_ctor_get(v___x_6494_, 4);
                v_env_6496_ = leanh::lean_ctor_get(v___x_6494_, 0);
                v_nextMacroScope_6497_ = leanh::lean_ctor_get(v___x_6494_, 1);
                v_ngen_6498_ = leanh::lean_ctor_get(v___x_6494_, 2);
                v_auxDeclNGen_6499_ = leanh::lean_ctor_get(v___x_6494_, 3);
                v_cache_6500_ = leanh::lean_ctor_get(v___x_6494_, 5);
                v_messages_6501_ = leanh::lean_ctor_get(v___x_6494_, 6);
                v_infoState_6502_ = leanh::lean_ctor_get(v___x_6494_, 7);
                v_snapshotTasks_6503_ = leanh::lean_ctor_get(v___x_6494_, 8);
                v_isSharedCheck_6533_ = (!leanh::lean_is_exclusive(v___x_6494_)) as u8;
                if v_isSharedCheck_6533_ == 0 {
                    v___x_6505_ = v___x_6494_;
                    v_isShared_6506_ = v_isSharedCheck_6533_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6503_);
                    leanh::lean_inc(v_infoState_6502_);
                    leanh::lean_inc(v_messages_6501_);
                    leanh::lean_inc(v_cache_6500_);
                    leanh::lean_inc(v_traceState_6495_);
                    leanh::lean_inc(v_auxDeclNGen_6499_);
                    leanh::lean_inc(v_ngen_6498_);
                    leanh::lean_inc(v_nextMacroScope_6497_);
                    leanh::lean_inc(v_env_6496_);
                    leanh::lean_dec(v___x_6494_);
                    v___x_6505_ = leanh::lean_box(0);
                    v_isShared_6506_ = v_isSharedCheck_6533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6507_ = leanh::lean_ctor_get_uint64(
                    v_traceState_6495_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6508_ = leanh::lean_ctor_get(v_traceState_6495_, 0);
                v_isSharedCheck_6532_ =
                    (!leanh::lean_is_exclusive(v_traceState_6495_)) as u8;
                if v_isSharedCheck_6532_ == 0 {
                    v___x_6510_ = v_traceState_6495_;
                    v_isShared_6511_ = v_isSharedCheck_6532_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_6508_);
                    leanh::lean_dec(v_traceState_6495_);
                    v___x_6510_ = leanh::lean_box(0);
                    v_isShared_6511_ = v_isSharedCheck_6532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6512_ = leanh::lean_box(0);
                v___x_6513_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__0);
                v___x_6514_ = 0;
                v___x_6515_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__1;
                v___x_6516_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_6516_, 0, v_cls_6481_);
                leanh::lean_ctor_set(v___x_6516_, 1, v___x_6512_);
                leanh::lean_ctor_set(v___x_6516_, 2, v___x_6515_);
                leanh::lean_ctor_set_float(
                    v___x_6516_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_6513_,
                );
                leanh::lean_ctor_set_float(
                    v___x_6516_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6513_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6516_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6514_,
                );
                v___x_6517_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___closed__2;
                v___x_6518_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6518_, 0, v___x_6516_);
                leanh::lean_ctor_set(v___x_6518_, 1, v_a_6490_);
                leanh::lean_ctor_set(v___x_6518_, 2, v___x_6517_);
                leanh::lean_inc(v_ref_6488_);
                v___x_6519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6519_, 0, v_ref_6488_);
                leanh::lean_ctor_set(v___x_6519_, 1, v___x_6518_);
                v___x_6520_ = l_Lean_PersistentArray_push___redArg(v_traces_6508_, v___x_6519_);
                if v_isShared_6511_ == 0 {
                    leanh::lean_ctor_set(v___x_6510_, 0, v___x_6520_);
                    v___x_6522_ = v___x_6510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6531_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6531_, 0, v___x_6520_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6531_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_6507_,
                    );
                    v___x_6522_ = v_reuseFailAlloc_6531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6506_ == 0 {
                    leanh::lean_ctor_set(v___x_6505_, 4, v___x_6522_);
                    v___x_6524_ = v___x_6505_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6530_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 0, v_env_6496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 1, v_nextMacroScope_6497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 2, v_ngen_6498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 3, v_auxDeclNGen_6499_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 4, v___x_6522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 5, v_cache_6500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 6, v_messages_6501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 7, v_infoState_6502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6530_, 8, v_snapshotTasks_6503_);
                    v___x_6524_ = v_reuseFailAlloc_6530_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6525_ = lean_st_ref_set(v___y_6486_, v___x_6524_);
                v___x_6526_ = leanh::lean_box(0);
                if v_isShared_6493_ == 0 {
                    leanh::lean_ctor_set(v___x_6492_, 0, v___x_6526_);
                    v___x_6528_ = v___x_6492_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 0, v___x_6526_);
                    v___x_6528_ = v_reuseFailAlloc_6529_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg___boxed(
    mut v_cls_6535_: *mut leanh::LeanObject,
    mut v_msg_6536_: *mut leanh::LeanObject,
    mut v___y_6537_: *mut leanh::LeanObject,
    mut v___y_6538_: *mut leanh::LeanObject,
    mut v___y_6539_: *mut leanh::LeanObject,
    mut v___y_6540_: *mut leanh::LeanObject,
    mut v___y_6541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6542_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(
            v_cls_6535_,
            v_msg_6536_,
            v___y_6537_,
            v___y_6538_,
            v___y_6539_,
            v___y_6540_,
        );
    leanh::lean_dec(v___y_6540_);
    leanh::lean_dec_ref(v___y_6539_);
    leanh::lean_dec(v___y_6538_);
    leanh::lean_dec_ref(v___y_6537_);
    return v_res_6542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(
    mut v___x_6543_: *mut leanh::LeanObject,
    mut v_sz_6544_: usize,
    mut v_i_6545_: usize,
    mut v_bs_6546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6547_: u8 = 0;
    let mut v_v_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: usize = 0;
    let mut v___x_6553_: usize = 0;
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6547_ = lean_usize_dec_lt(v_i_6545_, v_sz_6544_);
                if v___x_6547_ == 0 {
                    return v_bs_6546_;
                } else {
                    v_v_6548_ = lean_array_uget(v_bs_6546_, v_i_6545_);
                    v___x_6549_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6550_ = lean_array_uset(v_bs_6546_, v_i_6545_, v___x_6549_);
                    v___x_6551_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_reorder(v_v_6548_, v___x_6543_);
                    v___x_6552_ = 1usize;
                    v___x_6553_ = lean_usize_add(v_i_6545_, v___x_6552_);
                    v___x_6554_ = lean_array_uset(v_bs_x27_6550_, v_i_6545_, v___x_6551_);
                    v_i_6545_ = v___x_6553_;
                    v_bs_6546_ = v___x_6554_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12___boxed(
    mut v___x_6556_: *mut leanh::LeanObject,
    mut v_sz_6557_: *mut leanh::LeanObject,
    mut v_i_6558_: *mut leanh::LeanObject,
    mut v_bs_6559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6560_: usize = 0;
    let mut v_i_boxed_6561_: usize = 0;
    let mut v_res_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6560_ = leanh::lean_unbox_usize(v_sz_6557_);
    leanh::lean_dec(v_sz_6557_);
    v_i_boxed_6561_ = leanh::lean_unbox_usize(v_i_6558_);
    leanh::lean_dec(v_i_6558_);
    v_res_6562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_6556_, v_sz_boxed_6560_, v_i_boxed_6561_, v_bs_6559_);
    leanh::lean_dec_ref(v___x_6556_);
    return v_res_6562_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(
    mut v_as_6563_: *mut leanh::LeanObject,
    mut v_sz_6564_: usize,
    mut v_i_6565_: usize,
    mut v_b_6566_: *mut leanh::LeanObject,
    mut v___y_6567_: *mut leanh::LeanObject,
    mut v___y_6568_: *mut leanh::LeanObject,
    mut v___y_6569_: *mut leanh::LeanObject,
    mut v___y_6570_: *mut leanh::LeanObject,
    mut v___y_6571_: *mut leanh::LeanObject,
    mut v___y_6572_: *mut leanh::LeanObject,
    mut v___y_6573_: *mut leanh::LeanObject,
    mut v___y_6574_: *mut leanh::LeanObject,
    mut v___y_6575_: *mut leanh::LeanObject,
    mut v___y_6576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6578_: u8 = 0;
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: usize = 0;
    let mut v___x_6584_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6578_ = lean_usize_dec_lt(v_i_6565_, v_sz_6564_);
                if v___x_6578_ == 0 {
                    v___x_6579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6579_, 0, v_b_6566_);
                    return v___x_6579_;
                } else {
                    v_a_6580_ = lean_array_uget_borrowed(v_as_6563_, v_i_6565_);
                    leanh::lean_inc(v_a_6580_);
                    v___x_6581_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstr_assert(
                        v_a_6580_,
                        v___y_6567_,
                        v___y_6568_,
                        v___y_6569_,
                        v___y_6570_,
                        v___y_6571_,
                        v___y_6572_,
                        v___y_6573_,
                        v___y_6574_,
                        v___y_6575_,
                        v___y_6576_,
                    );
                    if leanh::lean_obj_tag(v___x_6581_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6581_, 1);
                        v___x_6582_ = leanh::lean_box(0);
                        v___x_6583_ = 1usize;
                        v___x_6584_ = lean_usize_add(v_i_6565_, v___x_6583_);
                        v_i_6565_ = v___x_6584_;
                        v_b_6566_ = v___x_6582_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6581_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15___boxed(
    mut v_as_6586_: *mut leanh::LeanObject,
    mut v_sz_6587_: *mut leanh::LeanObject,
    mut v_i_6588_: *mut leanh::LeanObject,
    mut v_b_6589_: *mut leanh::LeanObject,
    mut v___y_6590_: *mut leanh::LeanObject,
    mut v___y_6591_: *mut leanh::LeanObject,
    mut v___y_6592_: *mut leanh::LeanObject,
    mut v___y_6593_: *mut leanh::LeanObject,
    mut v___y_6594_: *mut leanh::LeanObject,
    mut v___y_6595_: *mut leanh::LeanObject,
    mut v___y_6596_: *mut leanh::LeanObject,
    mut v___y_6597_: *mut leanh::LeanObject,
    mut v___y_6598_: *mut leanh::LeanObject,
    mut v___y_6599_: *mut leanh::LeanObject,
    mut v___y_6600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6601_: usize = 0;
    let mut v_i_boxed_6602_: usize = 0;
    let mut v_res_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6601_ = leanh::lean_unbox_usize(v_sz_6587_);
    leanh::lean_dec(v_sz_6587_);
    v_i_boxed_6602_ = leanh::lean_unbox_usize(v_i_6588_);
    leanh::lean_dec(v_i_6588_);
    v_res_6603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v_as_6586_, v_sz_boxed_6601_, v_i_boxed_6602_, v_b_6589_, v___y_6590_, v___y_6591_, v___y_6592_, v___y_6593_, v___y_6594_, v___y_6595_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_);
    leanh::lean_dec(v___y_6599_);
    leanh::lean_dec_ref(v___y_6598_);
    leanh::lean_dec(v___y_6597_);
    leanh::lean_dec_ref(v___y_6596_);
    leanh::lean_dec(v___y_6595_);
    leanh::lean_dec_ref(v___y_6594_);
    leanh::lean_dec(v___y_6593_);
    leanh::lean_dec_ref(v___y_6592_);
    leanh::lean_dec(v___y_6591_);
    leanh::lean_dec(v___y_6590_);
    leanh::lean_dec_ref(v_as_6586_);
    return v_res_6603_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(
    mut v_as_6604_: *mut leanh::LeanObject,
    mut v_sz_6605_: usize,
    mut v_i_6606_: usize,
    mut v_b_6607_: *mut leanh::LeanObject,
    mut v___y_6608_: *mut leanh::LeanObject,
    mut v___y_6609_: *mut leanh::LeanObject,
    mut v___y_6610_: *mut leanh::LeanObject,
    mut v___y_6611_: *mut leanh::LeanObject,
    mut v___y_6612_: *mut leanh::LeanObject,
    mut v___y_6613_: *mut leanh::LeanObject,
    mut v___y_6614_: *mut leanh::LeanObject,
    mut v___y_6615_: *mut leanh::LeanObject,
    mut v___y_6616_: *mut leanh::LeanObject,
    mut v___y_6617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6619_: u8 = 0;
    let mut v___x_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: usize = 0;
    let mut v___x_6625_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6619_ = lean_usize_dec_lt(v_i_6606_, v_sz_6605_);
                if v___x_6619_ == 0 {
                    v___x_6620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6620_, 0, v_b_6607_);
                    return v___x_6620_;
                } else {
                    v_a_6621_ = lean_array_uget_borrowed(v_as_6604_, v_i_6606_);
                    leanh::lean_inc(v___y_6617_);
                    leanh::lean_inc_ref(v___y_6616_);
                    leanh::lean_inc(v___y_6615_);
                    leanh::lean_inc_ref(v___y_6614_);
                    leanh::lean_inc(v___y_6613_);
                    leanh::lean_inc_ref(v___y_6612_);
                    leanh::lean_inc(v___y_6611_);
                    leanh::lean_inc_ref(v___y_6610_);
                    leanh::lean_inc(v___y_6609_);
                    leanh::lean_inc(v___y_6608_);
                    leanh::lean_inc(v_a_6621_);
                    v___x_6622_ = lean_grind_cutsat_assert_le(
                        v_a_6621_,
                        v___y_6608_,
                        v___y_6609_,
                        v___y_6610_,
                        v___y_6611_,
                        v___y_6612_,
                        v___y_6613_,
                        v___y_6614_,
                        v___y_6615_,
                        v___y_6616_,
                        v___y_6617_,
                    );
                    if leanh::lean_obj_tag(v___x_6622_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6622_, 1);
                        v___x_6623_ = leanh::lean_box(0);
                        v___x_6624_ = 1usize;
                        v___x_6625_ = lean_usize_add(v_i_6606_, v___x_6624_);
                        v_i_6606_ = v___x_6625_;
                        v_b_6607_ = v___x_6623_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6622_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13___boxed(
    mut v_as_6627_: *mut leanh::LeanObject,
    mut v_sz_6628_: *mut leanh::LeanObject,
    mut v_i_6629_: *mut leanh::LeanObject,
    mut v_b_6630_: *mut leanh::LeanObject,
    mut v___y_6631_: *mut leanh::LeanObject,
    mut v___y_6632_: *mut leanh::LeanObject,
    mut v___y_6633_: *mut leanh::LeanObject,
    mut v___y_6634_: *mut leanh::LeanObject,
    mut v___y_6635_: *mut leanh::LeanObject,
    mut v___y_6636_: *mut leanh::LeanObject,
    mut v___y_6637_: *mut leanh::LeanObject,
    mut v___y_6638_: *mut leanh::LeanObject,
    mut v___y_6639_: *mut leanh::LeanObject,
    mut v___y_6640_: *mut leanh::LeanObject,
    mut v___y_6641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6642_: usize = 0;
    let mut v_i_boxed_6643_: usize = 0;
    let mut v_res_6644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6642_ = leanh::lean_unbox_usize(v_sz_6628_);
    leanh::lean_dec(v_sz_6628_);
    v_i_boxed_6643_ = leanh::lean_unbox_usize(v_i_6629_);
    leanh::lean_dec(v_i_6629_);
    v_res_6644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v_as_6627_, v_sz_boxed_6642_, v_i_boxed_6643_, v_b_6630_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
    leanh::lean_dec(v___y_6640_);
    leanh::lean_dec_ref(v___y_6639_);
    leanh::lean_dec(v___y_6638_);
    leanh::lean_dec_ref(v___y_6637_);
    leanh::lean_dec(v___y_6636_);
    leanh::lean_dec_ref(v___y_6635_);
    leanh::lean_dec(v___y_6634_);
    leanh::lean_dec_ref(v___y_6633_);
    leanh::lean_dec(v___y_6632_);
    leanh::lean_dec(v___y_6631_);
    leanh::lean_dec_ref(v_as_6627_);
    return v_res_6644_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(
    mut v_a_6645_: *mut leanh::LeanObject,
    mut v_a_6646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6652_: u8 = 0;
    let mut v___x_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_6645_) == 0 {
                    v___x_6647_ = l_List_reverse___redArg(v_a_6646_);
                    return v___x_6647_;
                } else {
                    v_head_6648_ = leanh::lean_ctor_get(v_a_6645_, 0);
                    v_tail_6649_ = leanh::lean_ctor_get(v_a_6645_, 1);
                    v_isSharedCheck_6660_ = (!leanh::lean_is_exclusive(v_a_6645_)) as u8;
                    if v_isSharedCheck_6660_ == 0 {
                        v___x_6651_ = v_a_6645_;
                        v_isShared_6652_ = v_isSharedCheck_6660_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6649_);
                        leanh::lean_inc(v_head_6648_);
                        leanh::lean_dec(v_a_6645_);
                        v___x_6651_ = leanh::lean_box(0);
                        v_isShared_6652_ = v_isSharedCheck_6660_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6653_ = l_Nat_reprFast(v_head_6648_);
                v___x_6654_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6654_, 0, v___x_6653_);
                v___x_6655_ = l_Lean_MessageData_ofFormat(v___x_6654_);
                if v_isShared_6652_ == 0 {
                    leanh::lean_ctor_set(v___x_6651_, 1, v_a_6646_);
                    leanh::lean_ctor_set(v___x_6651_, 0, v___x_6655_);
                    v___x_6657_ = v___x_6651_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6659_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6659_, 0, v___x_6655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6659_, 1, v_a_6646_);
                    v___x_6657_ = v_reuseFailAlloc_6659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6645_ = v_tail_6649_;
                v_a_6646_ = v___x_6657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(
    mut v_as_6661_: *mut leanh::LeanObject,
    mut v_sz_6662_: usize,
    mut v_i_6663_: usize,
    mut v_b_6664_: *mut leanh::LeanObject,
    mut v___y_6665_: *mut leanh::LeanObject,
    mut v___y_6666_: *mut leanh::LeanObject,
    mut v___y_6667_: *mut leanh::LeanObject,
    mut v___y_6668_: *mut leanh::LeanObject,
    mut v___y_6669_: *mut leanh::LeanObject,
    mut v___y_6670_: *mut leanh::LeanObject,
    mut v___y_6671_: *mut leanh::LeanObject,
    mut v___y_6672_: *mut leanh::LeanObject,
    mut v___y_6673_: *mut leanh::LeanObject,
    mut v___y_6674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6676_: u8 = 0;
    let mut v___x_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: usize = 0;
    let mut v___x_6682_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6676_ = lean_usize_dec_lt(v_i_6663_, v_sz_6662_);
                if v___x_6676_ == 0 {
                    v___x_6677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6677_, 0, v_b_6664_);
                    return v___x_6677_;
                } else {
                    v_a_6678_ = lean_array_uget_borrowed(v_as_6661_, v_i_6663_);
                    leanh::lean_inc_ref(v___y_6673_);
                    leanh::lean_inc(v_a_6678_);
                    v___x_6679_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(
                        v_a_6678_,
                        v___y_6665_,
                        v___y_6666_,
                        v___y_6667_,
                        v___y_6668_,
                        v___y_6669_,
                        v___y_6670_,
                        v___y_6671_,
                        v___y_6672_,
                        v___y_6673_,
                        v___y_6674_,
                    );
                    if leanh::lean_obj_tag(v___x_6679_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6679_, 1);
                        v___x_6680_ = leanh::lean_box(0);
                        v___x_6681_ = 1usize;
                        v___x_6682_ = lean_usize_add(v_i_6663_, v___x_6681_);
                        v_i_6663_ = v___x_6682_;
                        v_b_6664_ = v___x_6680_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6679_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11___boxed(
    mut v_as_6684_: *mut leanh::LeanObject,
    mut v_sz_6685_: *mut leanh::LeanObject,
    mut v_i_6686_: *mut leanh::LeanObject,
    mut v_b_6687_: *mut leanh::LeanObject,
    mut v___y_6688_: *mut leanh::LeanObject,
    mut v___y_6689_: *mut leanh::LeanObject,
    mut v___y_6690_: *mut leanh::LeanObject,
    mut v___y_6691_: *mut leanh::LeanObject,
    mut v___y_6692_: *mut leanh::LeanObject,
    mut v___y_6693_: *mut leanh::LeanObject,
    mut v___y_6694_: *mut leanh::LeanObject,
    mut v___y_6695_: *mut leanh::LeanObject,
    mut v___y_6696_: *mut leanh::LeanObject,
    mut v___y_6697_: *mut leanh::LeanObject,
    mut v___y_6698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6699_: usize = 0;
    let mut v_i_boxed_6700_: usize = 0;
    let mut v_res_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6699_ = leanh::lean_unbox_usize(v_sz_6685_);
    leanh::lean_dec(v_sz_6685_);
    v_i_boxed_6700_ = leanh::lean_unbox_usize(v_i_6686_);
    leanh::lean_dec(v_i_6686_);
    v_res_6701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v_as_6684_, v_sz_boxed_6699_, v_i_boxed_6700_, v_b_6687_, v___y_6688_, v___y_6689_, v___y_6690_, v___y_6691_, v___y_6692_, v___y_6693_, v___y_6694_, v___y_6695_, v___y_6696_, v___y_6697_);
    leanh::lean_dec(v___y_6697_);
    leanh::lean_dec_ref(v___y_6696_);
    leanh::lean_dec(v___y_6695_);
    leanh::lean_dec_ref(v___y_6694_);
    leanh::lean_dec(v___y_6693_);
    leanh::lean_dec_ref(v___y_6692_);
    leanh::lean_dec(v___y_6691_);
    leanh::lean_dec_ref(v___y_6690_);
    leanh::lean_dec(v___y_6689_);
    leanh::lean_dec(v___y_6688_);
    leanh::lean_dec_ref(v_as_6684_);
    return v_res_6701_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(
    mut v_as_6702_: *mut leanh::LeanObject,
    mut v_i_6703_: usize,
    mut v_stop_6704_: usize,
    mut v_b_6705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6706_: u8 = 0;
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: usize = 0;
    let mut v___x_6711_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6706_ = lean_usize_dec_eq(v_i_6703_, v_stop_6704_);
                if v___x_6706_ == 0 {
                    v___x_6707_ = lean_array_uget_borrowed(v_as_6702_, v_i_6703_);
                    v___x_6708_ = l_Lean_PersistentArray_toArray___redArg(v___x_6707_);
                    v___x_6709_ = l_Array_append___redArg(v_b_6705_, v___x_6708_);
                    leanh::lean_dec_ref(v___x_6708_);
                    v___x_6710_ = 1usize;
                    v___x_6711_ = lean_usize_add(v_i_6703_, v___x_6710_);
                    v_i_6703_ = v___x_6711_;
                    v_b_6705_ = v___x_6709_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6705_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27___boxed(
    mut v_as_6713_: *mut leanh::LeanObject,
    mut v_i_6714_: *mut leanh::LeanObject,
    mut v_stop_6715_: *mut leanh::LeanObject,
    mut v_b_6716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6717_: usize = 0;
    let mut v_stop_boxed_6718_: usize = 0;
    let mut v_res_6719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6717_ = leanh::lean_unbox_usize(v_i_6714_);
    leanh::lean_dec(v_i_6714_);
    v_stop_boxed_6718_ = leanh::lean_unbox_usize(v_stop_6715_);
    leanh::lean_dec(v_stop_6715_);
    v_res_6719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_as_6713_, v_i_boxed_6717_, v_stop_boxed_6718_, v_b_6716_);
    leanh::lean_dec_ref(v_as_6713_);
    return v_res_6719_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(
    mut v_x_6720_: *mut leanh::LeanObject,
    mut v_x_6721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6720_) == 0 {
        let mut v_cs_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6725_: u8 = 0;
        v_cs_6722_ = leanh::lean_ctor_get(v_x_6720_, 0);
        v___x_6723_ = leanh::lean_unsigned_to_nat(0);
        v___x_6724_ = lean_array_get_size(v_cs_6722_);
        v___x_6725_ = lean_nat_dec_lt(v___x_6723_, v___x_6724_);
        if v___x_6725_ == 0 {
            return v_x_6721_;
        } else {
            let mut v___x_6726_: u8 = 0;
            v___x_6726_ = lean_nat_dec_le(v___x_6724_, v___x_6724_);
            if v___x_6726_ == 0 {
                if v___x_6725_ == 0 {
                    return v_x_6721_;
                } else {
                    let mut v___x_6727_: usize = 0;
                    let mut v___x_6728_: usize = 0;
                    let mut v___x_6729_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6727_ = 0usize;
                    v___x_6728_ = lean_usize_of_nat(v___x_6724_);
                    v___x_6729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_6722_, v___x_6727_, v___x_6728_, v_x_6721_);
                    return v___x_6729_;
                }
            } else {
                let mut v___x_6730_: usize = 0;
                let mut v___x_6731_: usize = 0;
                let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6730_ = 0usize;
                v___x_6731_ = lean_usize_of_nat(v___x_6724_);
                v___x_6732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_6722_, v___x_6730_, v___x_6731_, v_x_6721_);
                return v___x_6732_;
            }
        }
    } else {
        let mut v_vs_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6736_: u8 = 0;
        v_vs_6733_ = leanh::lean_ctor_get(v_x_6720_, 0);
        v___x_6734_ = leanh::lean_unsigned_to_nat(0);
        v___x_6735_ = lean_array_get_size(v_vs_6733_);
        v___x_6736_ = lean_nat_dec_lt(v___x_6734_, v___x_6735_);
        if v___x_6736_ == 0 {
            return v_x_6721_;
        } else {
            let mut v___x_6737_: u8 = 0;
            v___x_6737_ = lean_nat_dec_le(v___x_6735_, v___x_6735_);
            if v___x_6737_ == 0 {
                if v___x_6736_ == 0 {
                    return v_x_6721_;
                } else {
                    let mut v___x_6738_: usize = 0;
                    let mut v___x_6739_: usize = 0;
                    let mut v___x_6740_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6738_ = 0usize;
                    v___x_6739_ = lean_usize_of_nat(v___x_6735_);
                    v___x_6740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_6733_, v___x_6738_, v___x_6739_, v_x_6721_);
                    return v___x_6740_;
                }
            } else {
                let mut v___x_6741_: usize = 0;
                let mut v___x_6742_: usize = 0;
                let mut v___x_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6741_ = 0usize;
                v___x_6742_ = lean_usize_of_nat(v___x_6735_);
                v___x_6743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_6733_, v___x_6741_, v___x_6742_, v_x_6721_);
                return v___x_6743_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(
    mut v_as_6744_: *mut leanh::LeanObject,
    mut v_i_6745_: usize,
    mut v_stop_6746_: usize,
    mut v_b_6747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6748_: u8 = 0;
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: usize = 0;
    let mut v___x_6752_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6748_ = lean_usize_dec_eq(v_i_6745_, v_stop_6746_);
                if v___x_6748_ == 0 {
                    v___x_6749_ = lean_array_uget_borrowed(v_as_6744_, v_i_6745_);
                    v___x_6750_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v___x_6749_, v_b_6747_);
                    v___x_6751_ = 1usize;
                    v___x_6752_ = lean_usize_add(v_i_6745_, v___x_6751_);
                    v_i_6745_ = v___x_6752_;
                    v_b_6747_ = v___x_6750_;
                    state = 0;
                    continue;
                } else {
                    return v_b_6747_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35___boxed(
    mut v_as_6754_: *mut leanh::LeanObject,
    mut v_i_6755_: *mut leanh::LeanObject,
    mut v_stop_6756_: *mut leanh::LeanObject,
    mut v_b_6757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6758_: usize = 0;
    let mut v_stop_boxed_6759_: usize = 0;
    let mut v_res_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6758_ = leanh::lean_unbox_usize(v_i_6755_);
    leanh::lean_dec(v_i_6755_);
    v_stop_boxed_6759_ = leanh::lean_unbox_usize(v_stop_6756_);
    leanh::lean_dec(v_stop_6756_);
    v_res_6760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_as_6754_, v_i_boxed_6758_, v_stop_boxed_6759_, v_b_6757_);
    leanh::lean_dec_ref(v_as_6754_);
    return v_res_6760_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28___boxed(
    mut v_x_6761_: *mut leanh::LeanObject,
    mut v_x_6762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6763_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_x_6761_, v_x_6762_);
    leanh::lean_dec_ref(v_x_6761_);
    return v_res_6763_;
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(
    mut v_x_6764_: *mut leanh::LeanObject,
    mut v_x_6765_: usize,
    mut v_x_6766_: usize,
    mut v_x_6767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_6764_) == 0 {
        let mut v_cs_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6770_: usize = 0;
        let mut v_j_6771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6773_: usize = 0;
        let mut v___x_6774_: usize = 0;
        let mut v___x_6775_: usize = 0;
        let mut v___x_6776_: usize = 0;
        let mut v___x_6777_: usize = 0;
        let mut v___x_6778_: usize = 0;
        let mut v___x_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6783_: u8 = 0;
        v_cs_6768_ = leanh::lean_ctor_get(v_x_6764_, 0);
        v___x_6769_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0_once), _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7_spec__18___closed__0);
        v___x_6770_ = lean_usize_shift_right(v_x_6765_, v_x_6766_);
        v_j_6771_ = lean_usize_to_nat(v___x_6770_);
        v___x_6772_ = lean_array_get_borrowed(v___x_6769_, v_cs_6768_, v_j_6771_);
        v___x_6773_ = 1usize;
        v___x_6774_ = lean_usize_shift_left(v___x_6773_, v_x_6766_);
        v___x_6775_ = lean_usize_sub(v___x_6774_, v___x_6773_);
        v___x_6776_ = lean_usize_land(v_x_6765_, v___x_6775_);
        v___x_6777_ = 5usize;
        v___x_6778_ = lean_usize_sub(v_x_6766_, v___x_6777_);
        v___x_6779_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v___x_6772_, v___x_6776_, v___x_6778_, v_x_6767_);
        v___x_6780_ = leanh::lean_unsigned_to_nat(1);
        v___x_6781_ = lean_nat_add(v_j_6771_, v___x_6780_);
        leanh::lean_dec(v_j_6771_);
        v___x_6782_ = lean_array_get_size(v_cs_6768_);
        v___x_6783_ = lean_nat_dec_lt(v___x_6781_, v___x_6782_);
        if v___x_6783_ == 0 {
            leanh::lean_dec(v___x_6781_);
            return v___x_6779_;
        } else {
            let mut v___x_6784_: u8 = 0;
            v___x_6784_ = lean_nat_dec_le(v___x_6782_, v___x_6782_);
            if v___x_6784_ == 0 {
                if v___x_6783_ == 0 {
                    leanh::lean_dec(v___x_6781_);
                    return v___x_6779_;
                } else {
                    let mut v___x_6785_: usize = 0;
                    let mut v___x_6786_: usize = 0;
                    let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6785_ = lean_usize_of_nat(v___x_6781_);
                    leanh::lean_dec(v___x_6781_);
                    v___x_6786_ = lean_usize_of_nat(v___x_6782_);
                    v___x_6787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_6768_, v___x_6785_, v___x_6786_, v___x_6779_);
                    return v___x_6787_;
                }
            } else {
                let mut v___x_6788_: usize = 0;
                let mut v___x_6789_: usize = 0;
                let mut v___x_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6788_ = lean_usize_of_nat(v___x_6781_);
                leanh::lean_dec(v___x_6781_);
                v___x_6789_ = lean_usize_of_nat(v___x_6782_);
                v___x_6790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26_spec__35(v_cs_6768_, v___x_6788_, v___x_6789_, v___x_6779_);
                return v___x_6790_;
            }
        }
    } else {
        let mut v_vs_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6794_: u8 = 0;
        v_vs_6791_ = leanh::lean_ctor_get(v_x_6764_, 0);
        v___x_6792_ = lean_usize_to_nat(v_x_6765_);
        v___x_6793_ = lean_array_get_size(v_vs_6791_);
        v___x_6794_ = lean_nat_dec_lt(v___x_6792_, v___x_6793_);
        if v___x_6794_ == 0 {
            leanh::lean_dec(v___x_6792_);
            return v_x_6767_;
        } else {
            let mut v___x_6795_: u8 = 0;
            v___x_6795_ = lean_nat_dec_le(v___x_6793_, v___x_6793_);
            if v___x_6795_ == 0 {
                if v___x_6794_ == 0 {
                    leanh::lean_dec(v___x_6792_);
                    return v_x_6767_;
                } else {
                    let mut v___x_6796_: usize = 0;
                    let mut v___x_6797_: usize = 0;
                    let mut v___x_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6796_ = lean_usize_of_nat(v___x_6792_);
                    leanh::lean_dec(v___x_6792_);
                    v___x_6797_ = lean_usize_of_nat(v___x_6793_);
                    v___x_6798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_6791_, v___x_6796_, v___x_6797_, v_x_6767_);
                    return v___x_6798_;
                }
            } else {
                let mut v___x_6799_: usize = 0;
                let mut v___x_6800_: usize = 0;
                let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6799_ = lean_usize_of_nat(v___x_6792_);
                leanh::lean_dec(v___x_6792_);
                v___x_6800_ = lean_usize_of_nat(v___x_6793_);
                v___x_6801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_vs_6791_, v___x_6799_, v___x_6800_, v_x_6767_);
                return v___x_6801_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26___boxed(
    mut v_x_6802_: *mut leanh::LeanObject,
    mut v_x_6803_: *mut leanh::LeanObject,
    mut v_x_6804_: *mut leanh::LeanObject,
    mut v_x_6805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_93075__boxed_6806_: usize = 0;
    let mut v_x_93076__boxed_6807_: usize = 0;
    let mut v_res_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_93075__boxed_6806_ = leanh::lean_unbox_usize(v_x_6803_);
    leanh::lean_dec(v_x_6803_);
    v_x_93076__boxed_6807_ = leanh::lean_unbox_usize(v_x_6804_);
    leanh::lean_dec(v_x_6804_);
    v_res_6808_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_x_6802_, v_x_93075__boxed_6806_, v_x_93076__boxed_6807_, v_x_6805_);
    leanh::lean_dec_ref(v_x_6802_);
    return v_res_6808_;
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(
    mut v_t_6809_: *mut leanh::LeanObject,
    mut v_init_6810_: *mut leanh::LeanObject,
    mut v_start_6811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: u8 = 0;
    v___x_6812_ = leanh::lean_unsigned_to_nat(0);
    v___x_6813_ = lean_nat_dec_eq(v_start_6811_, v___x_6812_);
    if v___x_6813_ == 0 {
        let mut v_root_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_shift_6816_: usize = 0;
        let mut v_tailOff_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6818_: u8 = 0;
        v_root_6814_ = leanh::lean_ctor_get(v_t_6809_, 0);
        v_tail_6815_ = leanh::lean_ctor_get(v_t_6809_, 1);
        v_shift_6816_ = leanh::lean_ctor_get_usize(v_t_6809_, 4);
        v_tailOff_6817_ = leanh::lean_ctor_get(v_t_6809_, 3);
        v___x_6818_ = lean_nat_dec_le(v_tailOff_6817_, v_start_6811_);
        if v___x_6818_ == 0 {
            let mut v___x_6819_: usize = 0;
            let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6822_: u8 = 0;
            v___x_6819_ = lean_usize_of_nat(v_start_6811_);
            v___x_6820_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__26(v_root_6814_, v___x_6819_, v_shift_6816_, v_init_6810_);
            v___x_6821_ = lean_array_get_size(v_tail_6815_);
            v___x_6822_ = lean_nat_dec_lt(v___x_6812_, v___x_6821_);
            if v___x_6822_ == 0 {
                return v___x_6820_;
            } else {
                let mut v___x_6823_: u8 = 0;
                v___x_6823_ = lean_nat_dec_le(v___x_6821_, v___x_6821_);
                if v___x_6823_ == 0 {
                    if v___x_6822_ == 0 {
                        return v___x_6820_;
                    } else {
                        let mut v___x_6824_: usize = 0;
                        let mut v___x_6825_: usize = 0;
                        let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_6824_ = 0usize;
                        v___x_6825_ = lean_usize_of_nat(v___x_6821_);
                        v___x_6826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_6815_, v___x_6824_, v___x_6825_, v___x_6820_);
                        return v___x_6826_;
                    }
                } else {
                    let mut v___x_6827_: usize = 0;
                    let mut v___x_6828_: usize = 0;
                    let mut v___x_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6827_ = 0usize;
                    v___x_6828_ = lean_usize_of_nat(v___x_6821_);
                    v___x_6829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_6815_, v___x_6827_, v___x_6828_, v___x_6820_);
                    return v___x_6829_;
                }
            }
        } else {
            let mut v___x_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6832_: u8 = 0;
            v___x_6830_ = lean_nat_sub(v_start_6811_, v_tailOff_6817_);
            v___x_6831_ = lean_array_get_size(v_tail_6815_);
            v___x_6832_ = lean_nat_dec_lt(v___x_6830_, v___x_6831_);
            if v___x_6832_ == 0 {
                leanh::lean_dec(v___x_6830_);
                return v_init_6810_;
            } else {
                let mut v___x_6833_: u8 = 0;
                v___x_6833_ = lean_nat_dec_le(v___x_6831_, v___x_6831_);
                if v___x_6833_ == 0 {
                    if v___x_6832_ == 0 {
                        leanh::lean_dec(v___x_6830_);
                        return v_init_6810_;
                    } else {
                        let mut v___x_6834_: usize = 0;
                        let mut v___x_6835_: usize = 0;
                        let mut v___x_6836_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_6834_ = lean_usize_of_nat(v___x_6830_);
                        leanh::lean_dec(v___x_6830_);
                        v___x_6835_ = lean_usize_of_nat(v___x_6831_);
                        v___x_6836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_6815_, v___x_6834_, v___x_6835_, v_init_6810_);
                        return v___x_6836_;
                    }
                } else {
                    let mut v___x_6837_: usize = 0;
                    let mut v___x_6838_: usize = 0;
                    let mut v___x_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6837_ = lean_usize_of_nat(v___x_6830_);
                    leanh::lean_dec(v___x_6830_);
                    v___x_6838_ = lean_usize_of_nat(v___x_6831_);
                    v___x_6839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_6815_, v___x_6837_, v___x_6838_, v_init_6810_);
                    return v___x_6839_;
                }
            }
        }
    } else {
        let mut v_root_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6844_: u8 = 0;
        v_root_6840_ = leanh::lean_ctor_get(v_t_6809_, 0);
        v_tail_6841_ = leanh::lean_ctor_get(v_t_6809_, 1);
        v___x_6842_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__28(v_root_6840_, v_init_6810_);
        v___x_6843_ = lean_array_get_size(v_tail_6841_);
        v___x_6844_ = lean_nat_dec_lt(v___x_6812_, v___x_6843_);
        if v___x_6844_ == 0 {
            return v___x_6842_;
        } else {
            let mut v___x_6845_: u8 = 0;
            v___x_6845_ = lean_nat_dec_le(v___x_6843_, v___x_6843_);
            if v___x_6845_ == 0 {
                if v___x_6844_ == 0 {
                    return v___x_6842_;
                } else {
                    let mut v___x_6846_: usize = 0;
                    let mut v___x_6847_: usize = 0;
                    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_6846_ = 0usize;
                    v___x_6847_ = lean_usize_of_nat(v___x_6843_);
                    v___x_6848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_6841_, v___x_6846_, v___x_6847_, v___x_6842_);
                    return v___x_6848_;
                }
            } else {
                let mut v___x_6849_: usize = 0;
                let mut v___x_6850_: usize = 0;
                let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_6849_ = 0usize;
                v___x_6850_ = lean_usize_of_nat(v___x_6843_);
                v___x_6851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9_spec__27(v_tail_6841_, v___x_6849_, v___x_6850_, v___x_6842_);
                return v___x_6851_;
            }
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9___boxed(
    mut v_t_6852_: *mut leanh::LeanObject,
    mut v_init_6853_: *mut leanh::LeanObject,
    mut v_start_6854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6855_ =
        l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(
            v_t_6852_,
            v_init_6853_,
            v_start_6854_,
        );
    leanh::lean_dec(v_start_6854_);
    leanh::lean_dec_ref(v_t_6852_);
    return v_res_6855_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6872_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6;
    v___x_6873_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__8;
    v___x_6874_ = l_Lean_Name_append(v___x_6873_, v___x_6872_);
    return v___x_6874_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6876_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__10;
    v___x_6877_ = l_Lean_stringToMessageData(v___x_6876_);
    return v___x_6877_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6879_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__12;
    v___x_6880_ = l_Lean_stringToMessageData(v___x_6879_);
    return v___x_6880_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(
    mut v_a_6881_: *mut leanh::LeanObject,
    mut v_a_6882_: *mut leanh::LeanObject,
    mut v_a_6883_: *mut leanh::LeanObject,
    mut v_a_6884_: *mut leanh::LeanObject,
    mut v_a_6885_: *mut leanh::LeanObject,
    mut v_a_6886_: *mut leanh::LeanObject,
    mut v_a_6887_: *mut leanh::LeanObject,
    mut v_a_6888_: *mut leanh::LeanObject,
    mut v_a_6889_: *mut leanh::LeanObject,
    mut v_a_6890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6896_: u8 = 0;
    let mut v_vars_6897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dvds_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: u8 = 0;
    let mut v___x_6904_: u8 = 0;
    let mut v___x_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6921_: usize = 0;
    let mut v___x_6922_: usize = 0;
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6925_: usize = 0;
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6928_: usize = 0;
    let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6930_: usize = 0;
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6933_: usize = 0;
    let mut v___x_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6935_: usize = 0;
    let mut v___x_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6938_: u8 = 0;
    let mut v___x_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: u8 = 0;
    let mut v___x_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: u8 = 0;
    let mut v___x_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6978_: u8 = 0;
    let mut v___x_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6982_: u8 = 0;
    let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6987_: u8 = 0;
    let mut v_a_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6991_: u8 = 0;
    let mut v___x_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6892_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_6881_, v_a_6889_);
                if leanh::lean_obj_tag(v___x_6892_) == 0 {
                    v_a_6893_ = leanh::lean_ctor_get(v___x_6892_, 0);
                    v_isSharedCheck_6987_ = (!leanh::lean_is_exclusive(v___x_6892_)) as u8;
                    if v_isSharedCheck_6987_ == 0 {
                        v___x_6895_ = v___x_6892_;
                        v_isShared_6896_ = v_isSharedCheck_6987_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6893_);
                        leanh::lean_dec(v___x_6892_);
                        v___x_6895_ = leanh::lean_box(0);
                        v_isShared_6896_ = v_isSharedCheck_6987_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6988_ = leanh::lean_ctor_get(v___x_6892_, 0);
                    v_isSharedCheck_6995_ = (!leanh::lean_is_exclusive(v___x_6892_)) as u8;
                    if v_isSharedCheck_6995_ == 0 {
                        v___x_6990_ = v___x_6892_;
                        v_isShared_6991_ = v_isSharedCheck_6995_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6988_);
                        leanh::lean_dec(v___x_6892_);
                        v___x_6990_ = leanh::lean_box(0);
                        v_isShared_6991_ = v_isSharedCheck_6995_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_6897_ = leanh::lean_ctor_get(v_a_6893_, 0);
                leanh::lean_inc_ref(v_vars_6897_);
                v_vars_x27_6898_ = leanh::lean_ctor_get(v_a_6893_, 2);
                leanh::lean_inc_ref(v_vars_x27_6898_);
                v_dvds_6899_ = leanh::lean_ctor_get(v_a_6893_, 6);
                leanh::lean_inc_ref(v_dvds_6899_);
                v_lowers_6900_ = leanh::lean_ctor_get(v_a_6893_, 7);
                leanh::lean_inc_ref(v_lowers_6900_);
                v_uppers_6901_ = leanh::lean_ctor_get(v_a_6893_, 8);
                leanh::lean_inc_ref(v_uppers_6901_);
                v_diseqs_6902_ = leanh::lean_ctor_get(v_a_6893_, 9);
                leanh::lean_inc_ref(v_diseqs_6902_);
                leanh::lean_dec(v_a_6893_);
                v___x_6903_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_6897_);
                leanh::lean_dec_ref(v_vars_6897_);
                if v___x_6903_ == 0 {
                    v___x_6904_ = l_Lean_PersistentArray_isEmpty___redArg(v_vars_x27_6898_);
                    leanh::lean_dec_ref(v_vars_x27_6898_);
                    if v___x_6904_ == 0 {
                        leanh::lean_dec_ref(v_diseqs_6902_);
                        leanh::lean_dec_ref(v_uppers_6901_);
                        leanh::lean_dec_ref(v_lowers_6900_);
                        leanh::lean_dec_ref(v_dvds_6899_);
                        v___x_6905_ = leanh::lean_box(0);
                        if v_isShared_6896_ == 0 {
                            leanh::lean_ctor_set(v___x_6895_, 0, v___x_6905_);
                            v___x_6907_ = v___x_6895_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6908_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6908_, 0, v___x_6905_);
                            v___x_6907_ = v_reuseFailAlloc_6908_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6895_);
                        v___x_6909_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(
                            v_a_6881_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_,
                            v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_,
                        );
                        if leanh::lean_obj_tag(v___x_6909_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6909_, 1);
                            v___x_6910_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_sortVars(v_a_6881_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_);
                            if leanh::lean_obj_tag(v___x_6910_) == 0 {
                                v_a_6911_ = leanh::lean_ctor_get(v___x_6910_, 0);
                                leanh::lean_inc_n(v_a_6911_, 2);
                                leanh::lean_dec_ref_known(v___x_6910_, 1);
                                v___x_6912_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars_0__Lean_Meta_Grind_Arith_Cutsat_mkPermInv(v_a_6911_);
                                leanh::lean_inc_ref_n(v___x_6912_, 2);
                                v___f_6913_ = leanh::lean_alloc_closure(
                                    l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    2,
                                    1,
                                );
                                leanh::lean_closure_set(v___f_6913_, 0, v___x_6912_);
                                v___f_6914_ = leanh::lean_alloc_closure(
                                    l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___lam__1___boxed
                                        as *mut core::ffi::c_void,
                                    4,
                                    3,
                                );
                                leanh::lean_closure_set(v___f_6914_, 0, v_a_6911_);
                                leanh::lean_closure_set(v___f_6914_, 1, v___f_6913_);
                                leanh::lean_closure_set(v___f_6914_, 2, v___x_6912_);
                                v___x_6915_ = leanh::lean_unsigned_to_nat(0);
                                v___x_6916_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__0;
                                v___x_6917_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__7(v_dvds_6899_, v___x_6916_, v___x_6915_);
                                leanh::lean_dec_ref(v_dvds_6899_);
                                v___x_6918_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_lowers_6900_, v___x_6916_, v___x_6915_);
                                leanh::lean_dec_ref(v_lowers_6900_);
                                v___x_6919_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                                v___x_6920_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_6919_, v___f_6914_, v_a_6881_);
                                if leanh::lean_obj_tag(v___x_6920_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_6920_, 1);
                                    v_sz_6921_ = lean_array_size(v___x_6917_);
                                    v___x_6922_ = 0usize;
                                    v___x_6923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__10(v___x_6912_, v_sz_6921_, v___x_6922_, v___x_6917_);
                                    v___x_6924_ = leanh::lean_box(0);
                                    v_sz_6925_ = lean_array_size(v___x_6923_);
                                    v___x_6926_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__11(v___x_6923_, v_sz_6925_, v___x_6922_, v___x_6924_, v_a_6881_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_);
                                    leanh::lean_dec_ref(v___x_6923_);
                                    if leanh::lean_obj_tag(v___x_6926_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_6926_, 1);
                                        v___x_6927_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__8(v_uppers_6901_, v___x_6918_, v___x_6915_);
                                        leanh::lean_dec_ref(v_uppers_6901_);
                                        v_sz_6928_ = lean_array_size(v___x_6927_);
                                        v___x_6929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__12(v___x_6912_, v_sz_6928_, v___x_6922_, v___x_6927_);
                                        v_sz_6930_ = lean_array_size(v___x_6929_);
                                        v___x_6931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__13(v___x_6929_, v_sz_6930_, v___x_6922_, v___x_6924_, v_a_6881_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_);
                                        leanh::lean_dec_ref(v___x_6929_);
                                        if leanh::lean_obj_tag(v___x_6931_) == 0 {
                                            leanh::lean_dec_ref_known(v___x_6931_, 1);
                                            v___x_6932_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__9(v_diseqs_6902_, v___x_6916_, v___x_6915_);
                                            leanh::lean_dec_ref(v_diseqs_6902_);
                                            v_sz_6933_ = lean_array_size(v___x_6932_);
                                            v___x_6934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__14(v___x_6912_, v_sz_6933_, v___x_6922_, v___x_6932_);
                                            v_sz_6935_ = lean_array_size(v___x_6934_);
                                            v___x_6936_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__15(v___x_6934_, v_sz_6935_, v___x_6922_, v___x_6924_, v_a_6881_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_);
                                            leanh::lean_dec_ref(v___x_6934_);
                                            if leanh::lean_obj_tag(v___x_6936_) == 0 {
                                                leanh::lean_dec_ref_known(v___x_6936_, 1);
                                                v_options_6937_ =
                                                    leanh::lean_ctor_get(v_a_6889_, 2);
                                                v_hasTrace_6938_ =
                                                    leanh::lean_ctor_get_uint8(
                                                        v_options_6937_,
                                                        (core::mem::size_of::<
                                                            *mut leanh::LeanObject,
                                                        >(
                                                        ) * 1)
                                                            as u32,
                                                    );
                                                if v_hasTrace_6938_ == 0 {
                                                    leanh::lean_dec_ref(v___x_6912_);
                                                    leanh::lean_dec(v_a_6911_);
                                                    v___x_6939_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(v_a_6881_, v_a_6882_, v_a_6883_, v_a_6884_, v_a_6885_, v_a_6886_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_);
                                                    return v___x_6939_;
                                                } else {
                                                    v_inheritedTraceOptions_6940_ =
                                                        leanh::lean_ctor_get(v_a_6889_, 13);
                                                    v___x_6941_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__6;
                                                    v___x_6966_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9);
                                                    v___x_6967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6940_, v_options_6937_, v___x_6966_);
                                                    if v___x_6967_ == 0 {
                                                        leanh::lean_dec(v_a_6911_);
                                                        v___y_6943_ = v_a_6881_;
                                                        v___y_6944_ = v_a_6882_;
                                                        v___y_6945_ = v_a_6883_;
                                                        v___y_6946_ = v_a_6884_;
                                                        v___y_6947_ = v_a_6885_;
                                                        v___y_6948_ = v_a_6886_;
                                                        v___y_6949_ = v_a_6887_;
                                                        v___y_6950_ = v_a_6888_;
                                                        v___y_6951_ = v_a_6889_;
                                                        v_options_6952_ = v_options_6937_;
                                                        v_inheritedTraceOptions_6953_ =
                                                            v_inheritedTraceOptions_6940_;
                                                        v___y_6954_ = v_a_6890_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        v___x_6968_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__13);
                                                        v___x_6969_ = lean_array_to_list(v_a_6911_);
                                                        v___x_6970_ = leanh::lean_box(0);
                                                        v___x_6971_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_6969_, v___x_6970_);
                                                        v___x_6972_ =
                                                            l_Lean_MessageData_ofList(v___x_6971_);
                                                        v___x_6973_ = leanh::lean_alloc_ctor(
                                                            7,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_6973_,
                                                            0,
                                                            v___x_6968_,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_6973_,
                                                            1,
                                                            v___x_6972_,
                                                        );
                                                        v___x_6974_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_6941_, v___x_6973_, v_a_6887_, v_a_6888_, v_a_6889_, v_a_6890_);
                                                        if leanh::lean_obj_tag(v___x_6974_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec_ref_known(
                                                                v___x_6974_,
                                                                1,
                                                            );
                                                            v___y_6943_ = v_a_6881_;
                                                            v___y_6944_ = v_a_6882_;
                                                            v___y_6945_ = v_a_6883_;
                                                            v___y_6946_ = v_a_6884_;
                                                            v___y_6947_ = v_a_6885_;
                                                            v___y_6948_ = v_a_6886_;
                                                            v___y_6949_ = v_a_6887_;
                                                            v___y_6950_ = v_a_6888_;
                                                            v___y_6951_ = v_a_6889_;
                                                            v_options_6952_ = v_options_6937_;
                                                            v_inheritedTraceOptions_6953_ =
                                                                v_inheritedTraceOptions_6940_;
                                                            v___y_6954_ = v_a_6890_;
                                                            state = 3;
                                                            continue;
                                                        } else {
                                                            leanh::lean_dec_ref(v___x_6912_);
                                                            return v___x_6974_;
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_6912_);
                                                leanh::lean_dec(v_a_6911_);
                                                return v___x_6936_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_6912_);
                                            leanh::lean_dec(v_a_6911_);
                                            leanh::lean_dec_ref(v_diseqs_6902_);
                                            return v___x_6931_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_6918_);
                                        leanh::lean_dec_ref(v___x_6912_);
                                        leanh::lean_dec(v_a_6911_);
                                        leanh::lean_dec_ref(v_diseqs_6902_);
                                        leanh::lean_dec_ref(v_uppers_6901_);
                                        return v___x_6926_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_6918_);
                                    leanh::lean_dec_ref(v___x_6917_);
                                    leanh::lean_dec_ref(v___x_6912_);
                                    leanh::lean_dec(v_a_6911_);
                                    leanh::lean_dec_ref(v_diseqs_6902_);
                                    leanh::lean_dec_ref(v_uppers_6901_);
                                    return v___x_6920_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_diseqs_6902_);
                                leanh::lean_dec_ref(v_uppers_6901_);
                                leanh::lean_dec_ref(v_lowers_6900_);
                                leanh::lean_dec_ref(v_dvds_6899_);
                                v_a_6975_ = leanh::lean_ctor_get(v___x_6910_, 0);
                                v_isSharedCheck_6982_ =
                                    (!leanh::lean_is_exclusive(v___x_6910_)) as u8;
                                if v_isSharedCheck_6982_ == 0 {
                                    v___x_6977_ = v___x_6910_;
                                    v_isShared_6978_ = v_isSharedCheck_6982_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6975_);
                                    leanh::lean_dec(v___x_6910_);
                                    v___x_6977_ = leanh::lean_box(0);
                                    v_isShared_6978_ = v_isSharedCheck_6982_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_diseqs_6902_);
                            leanh::lean_dec_ref(v_uppers_6901_);
                            leanh::lean_dec_ref(v_lowers_6900_);
                            leanh::lean_dec_ref(v_dvds_6899_);
                            return v___x_6909_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_diseqs_6902_);
                    leanh::lean_dec_ref(v_uppers_6901_);
                    leanh::lean_dec_ref(v_lowers_6900_);
                    leanh::lean_dec_ref(v_dvds_6899_);
                    leanh::lean_dec_ref(v_vars_x27_6898_);
                    v___x_6983_ = leanh::lean_box(0);
                    if v_isShared_6896_ == 0 {
                        leanh::lean_ctor_set(v___x_6895_, 0, v___x_6983_);
                        v___x_6985_ = v___x_6895_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_6986_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6986_, 0, v___x_6983_);
                        v___x_6985_ = v_reuseFailAlloc_6986_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6907_;
            }
            3 => {
                v___x_6955_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__9,
                );
                v___x_6956_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                    v_inheritedTraceOptions_6953_,
                    v_options_6952_,
                    v___x_6955_,
                );
                if v___x_6956_ == 0 {
                    leanh::lean_dec_ref(v___x_6912_);
                    v___x_6957_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(
                        v___y_6943_,
                        v___y_6944_,
                        v___y_6945_,
                        v___y_6946_,
                        v___y_6947_,
                        v___y_6948_,
                        v___y_6949_,
                        v___y_6950_,
                        v___y_6951_,
                        v___y_6954_,
                    );
                    return v___x_6957_;
                } else {
                    v___x_6958_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___closed__11,
                    );
                    v___x_6959_ = lean_array_to_list(v___x_6912_);
                    v___x_6960_ = leanh::lean_box(0);
                    v___x_6961_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__16(v___x_6959_, v___x_6960_);
                    v___x_6962_ = l_Lean_MessageData_ofList(v___x_6961_);
                    v___x_6963_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6963_, 0, v___x_6958_);
                    leanh::lean_ctor_set(v___x_6963_, 1, v___x_6962_);
                    v___x_6964_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(v___x_6941_, v___x_6963_, v___y_6949_, v___y_6950_, v___y_6951_, v___y_6954_);
                    if leanh::lean_obj_tag(v___x_6964_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6964_, 1);
                        v___x_6965_ = l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants(
                            v___y_6943_,
                            v___y_6944_,
                            v___y_6945_,
                            v___y_6946_,
                            v___y_6947_,
                            v___y_6948_,
                            v___y_6949_,
                            v___y_6950_,
                            v___y_6951_,
                            v___y_6954_,
                        );
                        return v___x_6965_;
                    } else {
                        return v___x_6964_;
                    }
                }
            }
            4 => {
                if v_isShared_6978_ == 0 {
                    v___x_6980_ = v___x_6977_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6981_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6981_, 0, v_a_6975_);
                    v___x_6980_ = v_reuseFailAlloc_6981_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6980_;
            }
            6 => {
                return v___x_6985_;
            }
            7 => {
                if v_isShared_6991_ == 0 {
                    v___x_6993_ = v___x_6990_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6994_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6994_, 0, v_a_6988_);
                    v___x_6993_ = v_reuseFailAlloc_6994_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_reorderVars___boxed(
    mut v_a_6996_: *mut leanh::LeanObject,
    mut v_a_6997_: *mut leanh::LeanObject,
    mut v_a_6998_: *mut leanh::LeanObject,
    mut v_a_6999_: *mut leanh::LeanObject,
    mut v_a_7000_: *mut leanh::LeanObject,
    mut v_a_7001_: *mut leanh::LeanObject,
    mut v_a_7002_: *mut leanh::LeanObject,
    mut v_a_7003_: *mut leanh::LeanObject,
    mut v_a_7004_: *mut leanh::LeanObject,
    mut v_a_7005_: *mut leanh::LeanObject,
    mut v_a_7006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7007_ = l_Lean_Meta_Grind_Arith_Cutsat_reorderVars(
        v_a_6996_, v_a_6997_, v_a_6998_, v_a_6999_, v_a_7000_, v_a_7001_, v_a_7002_, v_a_7003_,
        v_a_7004_, v_a_7005_,
    );
    leanh::lean_dec(v_a_7005_);
    leanh::lean_dec_ref(v_a_7004_);
    leanh::lean_dec(v_a_7003_);
    leanh::lean_dec_ref(v_a_7002_);
    leanh::lean_dec(v_a_7001_);
    leanh::lean_dec_ref(v_a_7000_);
    leanh::lean_dec(v_a_6999_);
    leanh::lean_dec_ref(v_a_6998_);
    leanh::lean_dec(v_a_6997_);
    leanh::lean_dec(v_a_6996_);
    return v_res_7007_;
}
pub unsafe fn l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0(
    mut v_00_u03b2_7008_: *mut leanh::LeanObject,
    mut v_00_u03c3_7009_: *mut leanh::LeanObject,
    mut v_pm_7010_: *mut leanh::LeanObject,
    mut v_f_7011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7012_ = l_Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0___redArg(v_pm_7010_, v_f_7011_);
    return v___x_7012_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(
    mut v_cls_7013_: *mut leanh::LeanObject,
    mut v_msg_7014_: *mut leanh::LeanObject,
    mut v___y_7015_: *mut leanh::LeanObject,
    mut v___y_7016_: *mut leanh::LeanObject,
    mut v___y_7017_: *mut leanh::LeanObject,
    mut v___y_7018_: *mut leanh::LeanObject,
    mut v___y_7019_: *mut leanh::LeanObject,
    mut v___y_7020_: *mut leanh::LeanObject,
    mut v___y_7021_: *mut leanh::LeanObject,
    mut v___y_7022_: *mut leanh::LeanObject,
    mut v___y_7023_: *mut leanh::LeanObject,
    mut v___y_7024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7026_ =
        l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___redArg(
            v_cls_7013_,
            v_msg_7014_,
            v___y_7021_,
            v___y_7022_,
            v___y_7023_,
            v___y_7024_,
        );
    return v___x_7026_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17___boxed(
    mut v_cls_7027_: *mut leanh::LeanObject,
    mut v_msg_7028_: *mut leanh::LeanObject,
    mut v___y_7029_: *mut leanh::LeanObject,
    mut v___y_7030_: *mut leanh::LeanObject,
    mut v___y_7031_: *mut leanh::LeanObject,
    mut v___y_7032_: *mut leanh::LeanObject,
    mut v___y_7033_: *mut leanh::LeanObject,
    mut v___y_7034_: *mut leanh::LeanObject,
    mut v___y_7035_: *mut leanh::LeanObject,
    mut v___y_7036_: *mut leanh::LeanObject,
    mut v___y_7037_: *mut leanh::LeanObject,
    mut v___y_7038_: *mut leanh::LeanObject,
    mut v___y_7039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7040_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__17(
        v_cls_7027_,
        v_msg_7028_,
        v___y_7029_,
        v___y_7030_,
        v___y_7031_,
        v___y_7032_,
        v___y_7033_,
        v___y_7034_,
        v___y_7035_,
        v___y_7036_,
        v___y_7037_,
        v___y_7038_,
    );
    leanh::lean_dec(v___y_7038_);
    leanh::lean_dec_ref(v___y_7037_);
    leanh::lean_dec(v___y_7036_);
    leanh::lean_dec_ref(v___y_7035_);
    leanh::lean_dec(v___y_7034_);
    leanh::lean_dec_ref(v___y_7033_);
    leanh::lean_dec(v___y_7032_);
    leanh::lean_dec_ref(v___y_7031_);
    leanh::lean_dec(v___y_7030_);
    leanh::lean_dec(v___y_7029_);
    return v_res_7040_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0___redArg(
    mut v_pm_7041_: *mut leanh::LeanObject,
    mut v_f_7042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7043_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_7042_, v_pm_7041_);
    return v___x_7043_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0(
    mut v_00_u03b2_7044_: *mut leanh::LeanObject,
    mut v_00_u03c3_7045_: *mut leanh::LeanObject,
    mut v_pm_7046_: *mut leanh::LeanObject,
    mut v_f_7047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7048_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_7047_, v_pm_7046_);
    return v___x_7048_;
}
pub unsafe fn l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1(
    mut v_00_u03b1_7049_: *mut leanh::LeanObject,
    mut v_00_u03b2_7050_: *mut leanh::LeanObject,
    mut v_00_u03c3_7051_: *mut leanh::LeanObject,
    mut v_f_7052_: *mut leanh::LeanObject,
    mut v_n_7053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7054_ = l_Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1___redArg(v_f_7052_, v_n_7053_);
    return v___x_7054_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(
    mut v_00_u03b1_7055_: *mut leanh::LeanObject,
    mut v_00_u03b2_7056_: *mut leanh::LeanObject,
    mut v_00_u03c3_7057_: *mut leanh::LeanObject,
    mut v_f_7058_: *mut leanh::LeanObject,
    mut v_sz_7059_: usize,
    mut v_i_7060_: usize,
    mut v_bs_7061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___redArg(v_f_7058_, v_sz_7059_, v_i_7060_, v_bs_7061_);
    return v___x_7062_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20___boxed(
    mut v_00_u03b1_7063_: *mut leanh::LeanObject,
    mut v_00_u03b2_7064_: *mut leanh::LeanObject,
    mut v_00_u03c3_7065_: *mut leanh::LeanObject,
    mut v_f_7066_: *mut leanh::LeanObject,
    mut v_sz_7067_: *mut leanh::LeanObject,
    mut v_i_7068_: *mut leanh::LeanObject,
    mut v_bs_7069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7070_: usize = 0;
    let mut v_i_boxed_7071_: usize = 0;
    let mut v_res_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7070_ = leanh::lean_unbox_usize(v_sz_7067_);
    leanh::lean_dec(v_sz_7067_);
    v_i_boxed_7071_ = leanh::lean_unbox_usize(v_i_7068_);
    leanh::lean_dec(v_i_7068_);
    v_res_7072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__20(v_00_u03b1_7063_, v_00_u03b2_7064_, v_00_u03c3_7065_, v_f_7066_, v_sz_boxed_7070_, v_i_boxed_7071_, v_bs_7069_);
    return v_res_7072_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(
    mut v_00_u03b1_7073_: *mut leanh::LeanObject,
    mut v_00_u03b2_7074_: *mut leanh::LeanObject,
    mut v_f_7075_: *mut leanh::LeanObject,
    mut v_as_7076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7077_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___redArg(v_f_7075_, v_as_7076_);
    return v___x_7077_;
}
pub unsafe fn l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21___boxed(
    mut v_00_u03b1_7078_: *mut leanh::LeanObject,
    mut v_00_u03b2_7079_: *mut leanh::LeanObject,
    mut v_f_7080_: *mut leanh::LeanObject,
    mut v_as_7081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7082_ = l_Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21(v_00_u03b1_7078_, v_00_u03b2_7079_, v_f_7080_, v_as_7081_);
    leanh::lean_dec_ref(v_as_7081_);
    return v_res_7082_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(
    mut v_00_u03b1_7083_: *mut leanh::LeanObject,
    mut v_00_u03b2_7084_: *mut leanh::LeanObject,
    mut v_f_7085_: *mut leanh::LeanObject,
    mut v_as_7086_: *mut leanh::LeanObject,
    mut v_i_7087_: *mut leanh::LeanObject,
    mut v_acc_7088_: *mut leanh::LeanObject,
    mut v_hle_7089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7090_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___redArg(v_f_7085_, v_as_7086_, v_i_7087_, v_acc_7088_);
    return v___x_7090_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41___boxed(
    mut v_00_u03b1_7091_: *mut leanh::LeanObject,
    mut v_00_u03b2_7092_: *mut leanh::LeanObject,
    mut v_f_7093_: *mut leanh::LeanObject,
    mut v_as_7094_: *mut leanh::LeanObject,
    mut v_i_7095_: *mut leanh::LeanObject,
    mut v_acc_7096_: *mut leanh::LeanObject,
    mut v_hle_7097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7098_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___at___00Array_mapM_x27___at___00Lean_PersistentHashMap_mapMAux___at___00Lean_PersistentHashMap_mapM___at___00Lean_PersistentHashMap_map___at___00Lean_Meta_Grind_Arith_Cutsat_reorderVars_spec__0_spec__0_spec__1_spec__21_spec__41(v_00_u03b1_7091_, v_00_u03b2_7092_, v_f_7093_, v_as_7094_, v_i_7095_, v_acc_7096_, v_hle_7097_);
    leanh::lean_dec_ref(v_as_7094_);
    return v_res_7098_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ReorderVars(builtin);
}