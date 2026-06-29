// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.Reify
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedLemmas Lean.Meta.LitValues
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_eqv, lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr6;
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_hash, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEqRefl;
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_getBitVecValue_x3f, l_Lean_Meta_getNatValue_x3f,
    runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVExpr::{
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVLogical::{
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVPred::{
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedLemmas::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas,
    l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    l_Std_Tactic_BVDecide_BVExpr_append___override___redArg,
    l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override,
    l_Std_Tactic_BVDecide_BVExpr_bin___override, l_Std_Tactic_BVDecide_BVExpr_extract___override,
    l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg,
    l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override,
    l_Std_Tactic_BVDecide_BVExpr_shiftRight___override, l_Std_Tactic_BVDecide_BVExpr_un___override,
};
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 102, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__1_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 112, 112, 101, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [114, 101, 112, 108, 105, 99, 97, 116, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 116, 114, 97, 99, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [98, 118, 95, 100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 112, 111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value) as *mut crate::leanh::LeanObject,13172393257619429686 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 108, 122, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value) as *mut crate::leanh::LeanObject,15757622114771770429 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 118, 101, 114, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value) as *mut crate::leanh::LeanObject,4526169109995817204 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value) as *mut crate::leanh::LeanObject,7578295756008745317 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 111, 116, 97, 116, 101, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value) as *mut crate::leanh::LeanObject,11355947627665432272 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 111, 116, 97, 116, 101, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value) as *mut crate::leanh::LeanObject,13324510433510274429 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 112, 108, 105, 99, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value) as *mut crate::leanh::LeanObject,1452365453976042474 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value) as *mut crate::leanh::LeanObject,10711138606260240846 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 109, 112, 108, 101, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 109, 112, 108, 101, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value) as *mut crate::leanh::LeanObject,5724983336967091206 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value) as *mut crate::leanh::LeanObject,12148653221863161512 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value) as *mut crate::leanh::LeanObject,105488867511536770 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 116, 114, 97, 99, 116, 76, 115, 98, 39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value) as *mut crate::leanh::LeanObject,1678572690935040303 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value) as *mut crate::leanh::LeanObject,7474321248668962373 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [104, 65, 112, 112, 101, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [72, 65, 112, 112, 101, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value) as *mut crate::leanh::LeanObject,2304392498378253193 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value) as *mut crate::leanh::LeanObject,16790970975024013749 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [72, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value) as *mut crate::leanh::LeanObject,5422698995969631099 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value) as *mut crate::leanh::LeanObject,11315714300293431604 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [72, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value) as *mut crate::leanh::LeanObject,12221703946232912343 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value) as *mut crate::leanh::LeanObject,4302041416438838709 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value) as *mut crate::leanh::LeanObject,13744984671752750173 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value) as *mut crate::leanh::LeanObject,9682224670061807480 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value) as *mut crate::leanh::LeanObject,11858238400308895562 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value) as *mut crate::leanh::LeanObject,6100819061652633370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 88, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 88, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value) as *mut crate::leanh::LeanObject,5661876967030703708 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value) as *mut crate::leanh::LeanObject,11995384298059439981 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value) as *mut crate::leanh::LeanObject,12657514296478584286 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value) as *mut crate::leanh::LeanObject,14441402839729941302 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value) as *mut crate::leanh::LeanObject,1264154450872014868 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 105, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 86, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,1893448420036949551 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [66, 86, 66, 105, 110, 79, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject,2052334966301458605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value) as *mut crate::leanh::LeanObject,8633590422926641219 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject,2052334966301458605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value) as *mut crate::leanh::LeanObject,16739768336988840329 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [120, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject,2052334966301458605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value) as *mut crate::leanh::LeanObject,12702694847026093380 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject,2052334966301458605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value) as *mut crate::leanh::LeanObject,14273346465055528428 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject,2052334966301458605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value) as *mut crate::leanh::LeanObject,5895671572980706882 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 100, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject,2052334966301458605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value) as *mut crate::leanh::LeanObject,10337161908347300449 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 109, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut crate::leanh::LeanObject,2052334966301458605 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value) as *mut crate::leanh::LeanObject,799197807962006713 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [120, 111, 114, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value) as *mut crate::leanh::LeanObject,4119725913644827105 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 100, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value) as *mut crate::leanh::LeanObject,12822667666627757489 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 117, 108, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value) as *mut crate::leanh::LeanObject,16232499424393338845 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 100, 105, 118, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value) as *mut crate::leanh::LeanObject,2041225626295441782 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 109, 111, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value) as *mut crate::leanh::LeanObject,7562298844190415718 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value) as *mut crate::leanh::LeanObject,6896204920017572293 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 104, 105, 102, 116, 76, 101, 102, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value) as *mut crate::leanh::LeanObject,8176945809791874937 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value: crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 115, 104, 105, 102, 116, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 98, 101, 101, 110, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 100, 46, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_shiftRight___override as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value) as *mut crate::leanh::LeanObject,16353154075727218503 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value) as *mut crate::leanh::LeanObject,7017916557232087512 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 101, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value) as *mut crate::leanh::LeanObject,14769465239096254100 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value) as *mut crate::leanh::LeanObject,9849265584244012391 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_value) as *mut crate::leanh::LeanObject,11601345789416316724 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 120, 116, 114, 97, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value) as *mut crate::leanh::LeanObject,646477182314419725 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value) as *mut crate::leanh::LeanObject,15761733860085307253 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value) as *mut crate::leanh::LeanObject,9255189395584251158 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [103, 101, 116, 76, 115, 98, 68, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value) as *mut crate::leanh::LeanObject,5617647646599728841 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [117, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,5394957827732845164 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value) as *mut crate::leanh::LeanObject,17296090230036971119 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value) as *mut crate::leanh::LeanObject,16093780639914376387 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value) as *mut crate::leanh::LeanObject,9753356465987597394 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value) as *mut crate::leanh::LeanObject,1655553077289932752 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value) as *mut crate::leanh::LeanObject,10425341760733586335 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value) as *mut crate::leanh::LeanObject,6148012076188572320 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value) as *mut crate::leanh::LeanObject,3186261684962074301 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [117, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value) as *mut crate::leanh::LeanObject,13103364627973585450 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 86, 85, 110, 79, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,3440452707255258700 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value) as *mut crate::leanh::LeanObject,5396454276475693598 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,3440452707255258700 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value) as *mut crate::leanh::LeanObject,9807480938810536989 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,3440452707255258700 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value) as *mut crate::leanh::LeanObject,18013547890344707440 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,3440452707255258700 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value) as *mut crate::leanh::LeanObject,15020990588075728728 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,3440452707255258700 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value) as *mut crate::leanh::LeanObject,13041317507303989844 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,3440452707255258700 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value) as *mut crate::leanh::LeanObject,744326716584575709 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut crate::leanh::LeanObject,3440452707255258700 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value) as *mut crate::leanh::LeanObject,4313869223568439254 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 78, 97, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value) as *mut crate::leanh::LeanObject,11604326280315543611 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut crate::leanh::LeanObject,14410340039599863083 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value) as *mut crate::leanh::LeanObject,11468030476923802729 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [114, 111, 116, 97, 116, 101, 76, 101, 102, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_value) as *mut crate::leanh::LeanObject,4477786134226854944 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 111, 116, 97, 116, 101, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value) as *mut crate::leanh::LeanObject,3973774320290730301 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 118, 101, 114, 115, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value) as *mut crate::leanh::LeanObject,6433797635050614710 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 108, 122, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value) as *mut crate::leanh::LeanObject,9523836033625423468 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 112, 111, 112, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut crate::leanh::LeanObject,5139300886809190733 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut crate::leanh::LeanObject,17363264175708149920 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,18076273821967539232 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut crate::leanh::LeanObject,403369037444587699 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value) as *mut crate::leanh::LeanObject,16094149021198470069 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(
    mut v_x_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
    mut v_a_2984_: *mut crate::leanh::LeanObject,
    mut v_a_2985_: *mut crate::leanh::LeanObject,
    mut v_a_2986_: *mut crate::leanh::LeanObject,
    mut v_a_2987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v_fst_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut v_a_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3012_: u8 = 0;
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3016_: u8 = 0;
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v___x_3018_: u8 = 0;
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_x_2982_);
                v___x_2989_ = l_Lean_Meta_getBitVecValue_x3f(
                    v_x_2982_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                );
                if crate::leanh::lean_obj_tag(v___x_2989_) == 0 {
                    v_a_2990_ = crate::leanh::lean_ctor_get(v___x_2989_, 0);
                    crate::leanh::lean_inc(v_a_2990_);
                    crate::leanh::lean_dec_ref_known(v___x_2989_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2990_) == 1 {
                        crate::leanh::lean_dec_ref(v_x_2982_);
                        v_val_2991_ = crate::leanh::lean_ctor_get(v_a_2990_, 0);
                        v_isSharedCheck_3017_ = (!crate::leanh::lean_is_exclusive(v_a_2990_)) as u8;
                        if v_isSharedCheck_3017_ == 0 {
                            v___x_2993_ = v_a_2990_;
                            v_isShared_2994_ = v_isSharedCheck_3017_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2991_);
                            crate::leanh::lean_dec(v_a_2990_);
                            v___x_2993_ = crate::leanh::lean_box(0);
                            v_isShared_2994_ = v_isSharedCheck_3017_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2990_);
                        v___x_3018_ = 0;
                        v___x_3019_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(
                            v_x_2982_,
                            v___x_3018_,
                            v_a_2983_,
                            v_a_2984_,
                            v_a_2985_,
                            v_a_2986_,
                            v_a_2987_,
                        );
                        return v___x_3019_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2982_);
                    v_a_3020_ = crate::leanh::lean_ctor_get(v___x_2989_, 0);
                    v_isSharedCheck_3027_ = (!crate::leanh::lean_is_exclusive(v___x_2989_)) as u8;
                    if v_isSharedCheck_3027_ == 0 {
                        v___x_3022_ = v___x_2989_;
                        v_isShared_3023_ = v_isSharedCheck_3027_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3020_);
                        crate::leanh::lean_dec(v___x_2989_);
                        v___x_3022_ = crate::leanh::lean_box(0);
                        v_isShared_3023_ = v_isSharedCheck_3027_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2995_ = crate::leanh::lean_ctor_get(v_val_2991_, 0);
                crate::leanh::lean_inc(v_fst_2995_);
                v_snd_2996_ = crate::leanh::lean_ctor_get(v_val_2991_, 1);
                crate::leanh::lean_inc(v_snd_2996_);
                crate::leanh::lean_dec(v_val_2991_);
                v___x_2997_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(
                    v_fst_2995_,
                    v_snd_2996_,
                );
                if crate::leanh::lean_obj_tag(v___x_2997_) == 0 {
                    v_a_2998_ = crate::leanh::lean_ctor_get(v___x_2997_, 0);
                    v_isSharedCheck_3008_ = (!crate::leanh::lean_is_exclusive(v___x_2997_)) as u8;
                    if v_isSharedCheck_3008_ == 0 {
                        v___x_3000_ = v___x_2997_;
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2998_);
                        crate::leanh::lean_dec(v___x_2997_);
                        v___x_3000_ = crate::leanh::lean_box(0);
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2993_);
                    v_a_3009_ = crate::leanh::lean_ctor_get(v___x_2997_, 0);
                    v_isSharedCheck_3016_ = (!crate::leanh::lean_is_exclusive(v___x_2997_)) as u8;
                    if v_isSharedCheck_3016_ == 0 {
                        v___x_3011_ = v___x_2997_;
                        v_isShared_3012_ = v_isSharedCheck_3016_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3009_);
                        crate::leanh::lean_dec(v___x_2997_);
                        v___x_3011_ = crate::leanh::lean_box(0);
                        v_isShared_3012_ = v_isSharedCheck_3016_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2993_, 0, v_a_2998_);
                    v___x_3003_ = v___x_2993_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3007_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3001_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3000_, 0, v___x_3003_);
                    v___x_3005_ = v___x_3000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
                    v___x_3005_ = v_reuseFailAlloc_3006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3005_;
            }
            5 => {
                if v_isShared_3012_ == 0 {
                    v___x_3014_ = v___x_3011_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
                    v___x_3014_ = v_reuseFailAlloc_3015_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3014_;
            }
            7 => {
                if v_isShared_3023_ == 0 {
                    v___x_3025_ = v___x_3022_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
                    v___x_3025_ = v_reuseFailAlloc_3026_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit___boxed(
    mut v_x_3028_: *mut crate::leanh::LeanObject,
    mut v_a_3029_: *mut crate::leanh::LeanObject,
    mut v_a_3030_: *mut crate::leanh::LeanObject,
    mut v_a_3031_: *mut crate::leanh::LeanObject,
    mut v_a_3032_: *mut crate::leanh::LeanObject,
    mut v_a_3033_: *mut crate::leanh::LeanObject,
    mut v_a_3034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3035_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_x_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
    crate::leanh::lean_dec(v_a_3033_);
    crate::leanh::lean_dec_ref(v_a_3032_);
    crate::leanh::lean_dec(v_a_3031_);
    crate::leanh::lean_dec_ref(v_a_3030_);
    crate::leanh::lean_dec(v_a_3029_);
    return v_res_3035_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(
    mut v___x_3036_: *mut crate::leanh::LeanObject,
    mut v_fst_3037_: *mut crate::leanh::LeanObject,
    mut v_fproof_3038_: *mut crate::leanh::LeanObject,
    mut v_snd_3039_: *mut crate::leanh::LeanObject,
    mut v_sproof_3040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_val_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3055_: u8 = 0;
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut v_val_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_fproof_3038_) == 0 {
                    crate::leanh::lean_dec_ref(v_snd_3039_);
                    if crate::leanh::lean_obj_tag(v_sproof_3040_) == 0 {
                        crate::leanh::lean_dec_ref(v_fst_3037_);
                        crate::leanh::lean_dec(v___x_3036_);
                        v___x_3041_ = crate::leanh::lean_box(0);
                        return v___x_3041_;
                    } else {
                        v_val_3042_ = crate::leanh::lean_ctor_get(v_sproof_3040_, 0);
                        v_isSharedCheck_3051_ =
                            (!crate::leanh::lean_is_exclusive(v_sproof_3040_)) as u8;
                        if v_isSharedCheck_3051_ == 0 {
                            v___x_3044_ = v_sproof_3040_;
                            v_isShared_3045_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3042_);
                            crate::leanh::lean_dec(v_sproof_3040_);
                            v___x_3044_ = crate::leanh::lean_box(0);
                            v_isShared_3045_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fst_3037_);
                    if crate::leanh::lean_obj_tag(v_sproof_3040_) == 0 {
                        v_val_3052_ = crate::leanh::lean_ctor_get(v_fproof_3038_, 0);
                        v_isSharedCheck_3061_ =
                            (!crate::leanh::lean_is_exclusive(v_fproof_3038_)) as u8;
                        if v_isSharedCheck_3061_ == 0 {
                            v___x_3054_ = v_fproof_3038_;
                            v_isShared_3055_ = v_isSharedCheck_3061_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3052_);
                            crate::leanh::lean_dec(v_fproof_3038_);
                            v___x_3054_ = crate::leanh::lean_box(0);
                            v_isShared_3055_ = v_isSharedCheck_3061_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_snd_3039_);
                        crate::leanh::lean_dec(v___x_3036_);
                        v_val_3062_ = crate::leanh::lean_ctor_get(v_fproof_3038_, 0);
                        crate::leanh::lean_inc(v_val_3062_);
                        crate::leanh::lean_dec_ref_known(v_fproof_3038_, 1);
                        v_val_3063_ = crate::leanh::lean_ctor_get(v_sproof_3040_, 0);
                        v_isSharedCheck_3071_ =
                            (!crate::leanh::lean_is_exclusive(v_sproof_3040_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_3065_ = v_sproof_3040_;
                            v_isShared_3066_ = v_isSharedCheck_3071_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3063_);
                            crate::leanh::lean_dec(v_sproof_3040_);
                            v___x_3065_ = crate::leanh::lean_box(0);
                            v_isShared_3066_ = v_isSharedCheck_3071_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3046_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_3036_, v_fst_3037_);
                v___x_3047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3047_, 0, v___x_3046_);
                crate::leanh::lean_ctor_set(v___x_3047_, 1, v_val_3042_);
                if v_isShared_3045_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3047_);
                    v___x_3049_ = v___x_3044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
                    v___x_3049_ = v_reuseFailAlloc_3050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3049_;
            }
            3 => {
                v___x_3056_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_3036_, v_snd_3039_);
                v___x_3057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3057_, 0, v_val_3052_);
                crate::leanh::lean_ctor_set(v___x_3057_, 1, v___x_3056_);
                if v_isShared_3055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3054_, 0, v___x_3057_);
                    v___x_3059_ = v___x_3054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
                    v___x_3059_ = v_reuseFailAlloc_3060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3059_;
            }
            5 => {
                v___x_3067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3067_, 0, v_val_3062_);
                crate::leanh::lean_ctor_set(v___x_3067_, 1, v_val_3063_);
                if v_isShared_3066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3065_, 0, v___x_3067_);
                    v___x_3069_ = v___x_3065_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
                    v___x_3069_ = v_reuseFailAlloc_3070_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(
    mut v_lhs_3072_: *mut crate::leanh::LeanObject,
    mut v_rhs_3073_: *mut crate::leanh::LeanObject,
    mut v_lhsExpr_3074_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_3075_: *mut crate::leanh::LeanObject,
    mut v_congrThm_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
    mut v_a_3079_: *mut crate::leanh::LeanObject,
    mut v_a_3080_: *mut crate::leanh::LeanObject,
    mut v_a_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_width_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v_fst_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3117_: u8 = 0;
    let mut v_a_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut v_a_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_width_3083_ = crate::leanh::lean_ctor_get(v_lhs_3072_, 0);
                crate::leanh::lean_inc_n(v_width_3083_, 2);
                v_expr_3084_ = crate::leanh::lean_ctor_get(v_lhs_3072_, 4);
                crate::leanh::lean_inc_ref(v_expr_3084_);
                v___x_3085_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3083_,
                    v_expr_3084_,
                    v_a_3077_,
                    v_a_3078_,
                    v_a_3079_,
                    v_a_3080_,
                    v_a_3081_,
                );
                if crate::leanh::lean_obj_tag(v___x_3085_) == 0 {
                    v_a_3086_ = crate::leanh::lean_ctor_get(v___x_3085_, 0);
                    crate::leanh::lean_inc(v_a_3086_);
                    crate::leanh::lean_dec_ref_known(v___x_3085_, 1);
                    v_width_3087_ = crate::leanh::lean_ctor_get(v_rhs_3073_, 0);
                    v_expr_3088_ = crate::leanh::lean_ctor_get(v_rhs_3073_, 4);
                    crate::leanh::lean_inc_ref(v_expr_3088_);
                    crate::leanh::lean_inc(v_width_3087_);
                    v___x_3089_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                        v_width_3087_,
                        v_expr_3088_,
                        v_a_3077_,
                        v_a_3078_,
                        v_a_3079_,
                        v_a_3080_,
                        v_a_3081_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3089_) == 0 {
                        v_a_3090_ = crate::leanh::lean_ctor_get(v___x_3089_, 0);
                        crate::leanh::lean_inc(v_a_3090_);
                        crate::leanh::lean_dec_ref_known(v___x_3089_, 1);
                        v___x_3091_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                            v_lhs_3072_,
                            v_a_3077_,
                            v_a_3078_,
                            v_a_3079_,
                            v_a_3080_,
                            v_a_3081_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3091_) == 0 {
                            v_a_3092_ = crate::leanh::lean_ctor_get(v___x_3091_, 0);
                            crate::leanh::lean_inc(v_a_3092_);
                            crate::leanh::lean_dec_ref_known(v___x_3091_, 1);
                            v___x_3093_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                                v_rhs_3073_,
                                v_a_3077_,
                                v_a_3078_,
                                v_a_3079_,
                                v_a_3080_,
                                v_a_3081_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3093_) == 0 {
                                v_a_3094_ = crate::leanh::lean_ctor_get(v___x_3093_, 0);
                                v_isSharedCheck_3117_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3093_)) as u8;
                                if v_isSharedCheck_3117_ == 0 {
                                    v___x_3096_ = v___x_3093_;
                                    v_isShared_3097_ = v_isSharedCheck_3117_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3094_);
                                    crate::leanh::lean_dec(v___x_3093_);
                                    v___x_3096_ = crate::leanh::lean_box(0);
                                    v_isShared_3097_ = v_isSharedCheck_3117_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3092_);
                                crate::leanh::lean_dec(v_a_3090_);
                                crate::leanh::lean_dec(v_a_3086_);
                                crate::leanh::lean_dec(v_width_3083_);
                                crate::leanh::lean_dec_ref(v_congrThm_3076_);
                                crate::leanh::lean_dec_ref(v_rhsExpr_3075_);
                                crate::leanh::lean_dec_ref(v_lhsExpr_3074_);
                                return v___x_3093_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3090_);
                            crate::leanh::lean_dec(v_a_3086_);
                            crate::leanh::lean_dec(v_width_3083_);
                            crate::leanh::lean_dec_ref(v_congrThm_3076_);
                            crate::leanh::lean_dec_ref(v_rhsExpr_3075_);
                            crate::leanh::lean_dec_ref(v_lhsExpr_3074_);
                            crate::leanh::lean_dec_ref(v_rhs_3073_);
                            return v___x_3091_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3086_);
                        crate::leanh::lean_dec(v_width_3083_);
                        crate::leanh::lean_dec_ref(v_congrThm_3076_);
                        crate::leanh::lean_dec_ref(v_rhsExpr_3075_);
                        crate::leanh::lean_dec_ref(v_lhsExpr_3074_);
                        crate::leanh::lean_dec_ref(v_rhs_3073_);
                        crate::leanh::lean_dec_ref(v_lhs_3072_);
                        v_a_3118_ = crate::leanh::lean_ctor_get(v___x_3089_, 0);
                        v_isSharedCheck_3125_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3089_)) as u8;
                        if v_isSharedCheck_3125_ == 0 {
                            v___x_3120_ = v___x_3089_;
                            v_isShared_3121_ = v_isSharedCheck_3125_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3118_);
                            crate::leanh::lean_dec(v___x_3089_);
                            v___x_3120_ = crate::leanh::lean_box(0);
                            v_isShared_3121_ = v_isSharedCheck_3125_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_width_3083_);
                    crate::leanh::lean_dec_ref(v_congrThm_3076_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_3075_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_3074_);
                    crate::leanh::lean_dec_ref(v_rhs_3073_);
                    crate::leanh::lean_dec_ref(v_lhs_3072_);
                    v_a_3126_ = crate::leanh::lean_ctor_get(v___x_3085_, 0);
                    v_isSharedCheck_3133_ = (!crate::leanh::lean_is_exclusive(v___x_3085_)) as u8;
                    if v_isSharedCheck_3133_ == 0 {
                        v___x_3128_ = v___x_3085_;
                        v_isShared_3129_ = v_isSharedCheck_3133_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3126_);
                        crate::leanh::lean_dec(v___x_3085_);
                        v___x_3128_ = crate::leanh::lean_box(0);
                        v_isShared_3129_ = v_isSharedCheck_3133_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_3090_);
                crate::leanh::lean_inc(v_a_3086_);
                v___x_3098_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(v_width_3083_, v_a_3086_, v_a_3092_, v_a_3090_, v_a_3094_);
                if crate::leanh::lean_obj_tag(v___x_3098_) == 1 {
                    v_val_3099_ = crate::leanh::lean_ctor_get(v___x_3098_, 0);
                    v_isSharedCheck_3112_ = (!crate::leanh::lean_is_exclusive(v___x_3098_)) as u8;
                    if v_isSharedCheck_3112_ == 0 {
                        v___x_3101_ = v___x_3098_;
                        v_isShared_3102_ = v_isSharedCheck_3112_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3099_);
                        crate::leanh::lean_dec(v___x_3098_);
                        v___x_3101_ = crate::leanh::lean_box(0);
                        v_isShared_3102_ = v_isSharedCheck_3112_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3098_);
                    crate::leanh::lean_dec(v_a_3090_);
                    crate::leanh::lean_dec(v_a_3086_);
                    crate::leanh::lean_dec_ref(v_congrThm_3076_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_3075_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_3074_);
                    v___x_3113_ = crate::leanh::lean_box(0);
                    if v_isShared_3097_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3096_, 0, v___x_3113_);
                        v___x_3115_ = v___x_3096_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3116_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
                        v___x_3115_ = v_reuseFailAlloc_3116_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3103_ = crate::leanh::lean_ctor_get(v_val_3099_, 0);
                crate::leanh::lean_inc(v_fst_3103_);
                v_snd_3104_ = crate::leanh::lean_ctor_get(v_val_3099_, 1);
                crate::leanh::lean_inc(v_snd_3104_);
                crate::leanh::lean_dec(v_val_3099_);
                v___x_3105_ = l_Lean_mkApp6(
                    v_congrThm_3076_,
                    v_lhsExpr_3074_,
                    v_rhsExpr_3075_,
                    v_a_3086_,
                    v_a_3090_,
                    v_fst_3103_,
                    v_snd_3104_,
                );
                if v_isShared_3102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3101_, 0, v___x_3105_);
                    v___x_3107_ = v___x_3101_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3111_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3097_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3096_, 0, v___x_3107_);
                    v___x_3109_ = v___x_3096_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
                    v___x_3109_ = v_reuseFailAlloc_3110_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3109_;
            }
            5 => {
                return v___x_3115_;
            }
            6 => {
                if v_isShared_3121_ == 0 {
                    v___x_3123_ = v___x_3120_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3123_;
            }
            8 => {
                if v_isShared_3129_ == 0 {
                    v___x_3131_ = v___x_3128_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
                    v___x_3131_ = v_reuseFailAlloc_3132_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed(
    mut v_lhs_3134_: *mut crate::leanh::LeanObject,
    mut v_rhs_3135_: *mut crate::leanh::LeanObject,
    mut v_lhsExpr_3136_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_3137_: *mut crate::leanh::LeanObject,
    mut v_congrThm_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
    mut v_a_3143_: *mut crate::leanh::LeanObject,
    mut v_a_3144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(v_lhs_3134_, v_rhs_3135_, v_lhsExpr_3136_, v_rhsExpr_3137_, v_congrThm_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
    crate::leanh::lean_dec(v_a_3143_);
    crate::leanh::lean_dec_ref(v_a_3142_);
    crate::leanh::lean_dec(v_a_3141_);
    crate::leanh::lean_dec_ref(v_a_3140_);
    crate::leanh::lean_dec(v_a_3139_);
    return v_res_3145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(
    mut v_inner_3146_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_3147_: *mut crate::leanh::LeanObject,
    mut v_congrProof_3148_: *mut crate::leanh::LeanObject,
    mut v_a_3149_: *mut crate::leanh::LeanObject,
    mut v_a_3150_: *mut crate::leanh::LeanObject,
    mut v_a_3151_: *mut crate::leanh::LeanObject,
    mut v_a_3152_: *mut crate::leanh::LeanObject,
    mut v_a_3153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_width_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v_val_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3167_: u8 = 0;
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v_a_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_width_3155_ = crate::leanh::lean_ctor_get(v_inner_3146_, 0);
                crate::leanh::lean_inc_n(v_width_3155_, 2);
                v_expr_3156_ = crate::leanh::lean_ctor_get(v_inner_3146_, 4);
                crate::leanh::lean_inc_ref(v_expr_3156_);
                v___x_3157_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3155_,
                    v_expr_3156_,
                    v_a_3149_,
                    v_a_3150_,
                    v_a_3151_,
                    v_a_3152_,
                    v_a_3153_,
                );
                if crate::leanh::lean_obj_tag(v___x_3157_) == 0 {
                    v_a_3158_ = crate::leanh::lean_ctor_get(v___x_3157_, 0);
                    crate::leanh::lean_inc(v_a_3158_);
                    crate::leanh::lean_dec_ref_known(v___x_3157_, 1);
                    v___x_3159_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                        v_inner_3146_,
                        v_a_3149_,
                        v_a_3150_,
                        v_a_3151_,
                        v_a_3152_,
                        v_a_3153_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3159_) == 0 {
                        v_a_3160_ = crate::leanh::lean_ctor_get(v___x_3159_, 0);
                        v_isSharedCheck_3181_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3159_)) as u8;
                        if v_isSharedCheck_3181_ == 0 {
                            v___x_3162_ = v___x_3159_;
                            v_isShared_3163_ = v_isSharedCheck_3181_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3160_);
                            crate::leanh::lean_dec(v___x_3159_);
                            v___x_3162_ = crate::leanh::lean_box(0);
                            v_isShared_3163_ = v_isSharedCheck_3181_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3158_);
                        crate::leanh::lean_dec(v_width_3155_);
                        crate::leanh::lean_dec_ref(v_congrProof_3148_);
                        crate::leanh::lean_dec_ref(v_innerExpr_3147_);
                        return v___x_3159_;
                    }
                } else {
                    crate::leanh::lean_dec(v_width_3155_);
                    crate::leanh::lean_dec_ref(v_congrProof_3148_);
                    crate::leanh::lean_dec_ref(v_innerExpr_3147_);
                    crate::leanh::lean_dec_ref(v_inner_3146_);
                    v_a_3182_ = crate::leanh::lean_ctor_get(v___x_3157_, 0);
                    v_isSharedCheck_3189_ = (!crate::leanh::lean_is_exclusive(v___x_3157_)) as u8;
                    if v_isSharedCheck_3189_ == 0 {
                        v___x_3184_ = v___x_3157_;
                        v_isShared_3185_ = v_isSharedCheck_3189_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3182_);
                        crate::leanh::lean_dec(v___x_3157_);
                        v___x_3184_ = crate::leanh::lean_box(0);
                        v_isShared_3185_ = v_isSharedCheck_3189_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3160_) == 1 {
                    v_val_3164_ = crate::leanh::lean_ctor_get(v_a_3160_, 0);
                    v_isSharedCheck_3176_ = (!crate::leanh::lean_is_exclusive(v_a_3160_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3166_ = v_a_3160_;
                        v_isShared_3167_ = v_isSharedCheck_3176_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3164_);
                        crate::leanh::lean_dec(v_a_3160_);
                        v___x_3166_ = crate::leanh::lean_box(0);
                        v_isShared_3167_ = v_isSharedCheck_3176_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3160_);
                    crate::leanh::lean_dec(v_a_3158_);
                    crate::leanh::lean_dec(v_width_3155_);
                    crate::leanh::lean_dec_ref(v_congrProof_3148_);
                    crate::leanh::lean_dec_ref(v_innerExpr_3147_);
                    v___x_3177_ = crate::leanh::lean_box(0);
                    if v_isShared_3163_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3162_, 0, v___x_3177_);
                        v___x_3179_ = v___x_3162_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
                        v___x_3179_ = v_reuseFailAlloc_3180_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3168_ = l_Lean_mkNatLit(v_width_3155_);
                v___x_3169_ = l_Lean_mkApp4(
                    v_congrProof_3148_,
                    v___x_3168_,
                    v_innerExpr_3147_,
                    v_a_3158_,
                    v_val_3164_,
                );
                if v_isShared_3167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3169_);
                    v___x_3171_ = v___x_3166_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3169_);
                    v___x_3171_ = v_reuseFailAlloc_3175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3162_, 0, v___x_3171_);
                    v___x_3173_ = v___x_3162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
                    v___x_3173_ = v_reuseFailAlloc_3174_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3173_;
            }
            5 => {
                return v___x_3179_;
            }
            6 => {
                if v_isShared_3185_ == 0 {
                    v___x_3187_ = v___x_3184_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
                    v___x_3187_ = v_reuseFailAlloc_3188_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed(
    mut v_inner_3190_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_3191_: *mut crate::leanh::LeanObject,
    mut v_congrProof_3192_: *mut crate::leanh::LeanObject,
    mut v_a_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
    mut v_a_3195_: *mut crate::leanh::LeanObject,
    mut v_a_3196_: *mut crate::leanh::LeanObject,
    mut v_a_3197_: *mut crate::leanh::LeanObject,
    mut v_a_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3199_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(v_inner_3190_, v_innerExpr_3191_, v_congrProof_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
    crate::leanh::lean_dec(v_a_3197_);
    crate::leanh::lean_dec_ref(v_a_3196_);
    crate::leanh::lean_dec(v_a_3195_);
    crate::leanh::lean_dec_ref(v_a_3194_);
    crate::leanh::lean_dec(v_a_3193_);
    return v_res_3199_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(
    mut v_a_3200_: *mut crate::leanh::LeanObject,
    mut v_x_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3201_) == 0 {
                    v___x_3202_ = crate::leanh::lean_box(0);
                    return v___x_3202_;
                } else {
                    v_key_3203_ = crate::leanh::lean_ctor_get(v_x_3201_, 0);
                    v_value_3204_ = crate::leanh::lean_ctor_get(v_x_3201_, 1);
                    v_tail_3205_ = crate::leanh::lean_ctor_get(v_x_3201_, 2);
                    v___x_3206_ = lean_expr_eqv(v_key_3203_, v_a_3200_);
                    if v___x_3206_ == 0 {
                        v_x_3201_ = v_tail_3205_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3204_);
                        v___x_3208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3208_, 0, v_value_3204_);
                        return v___x_3208_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(
    mut v_a_3209_: *mut crate::leanh::LeanObject,
    mut v_x_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3211_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_3209_, v_x_3210_);
    crate::leanh::lean_dec(v_x_3210_);
    crate::leanh::lean_dec_ref(v_a_3209_);
    return v_res_3211_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(
    mut v_m_3212_: *mut crate::leanh::LeanObject,
    mut v_a_3213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: u64 = 0;
    let mut v___x_3217_: u64 = 0;
    let mut v___x_3218_: u64 = 0;
    let mut v_fold_3219_: u64 = 0;
    let mut v___x_3220_: u64 = 0;
    let mut v___x_3221_: u64 = 0;
    let mut v___x_3222_: u64 = 0;
    let mut v___x_3223_: usize = 0;
    let mut v___x_3224_: usize = 0;
    let mut v___x_3225_: usize = 0;
    let mut v___x_3226_: usize = 0;
    let mut v___x_3227_: usize = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3214_ = crate::leanh::lean_ctor_get(v_m_3212_, 1);
    v___x_3215_ = lean_array_get_size(v_buckets_3214_);
    v___x_3216_ = l_Lean_Expr_hash(v_a_3213_);
    v___x_3217_ = 32u64;
    v___x_3218_ = lean_uint64_shift_right(v___x_3216_, v___x_3217_);
    v_fold_3219_ = lean_uint64_xor(v___x_3216_, v___x_3218_);
    v___x_3220_ = 16u64;
    v___x_3221_ = lean_uint64_shift_right(v_fold_3219_, v___x_3220_);
    v___x_3222_ = lean_uint64_xor(v_fold_3219_, v___x_3221_);
    v___x_3223_ = lean_uint64_to_usize(v___x_3222_);
    v___x_3224_ = lean_usize_of_nat(v___x_3215_);
    v___x_3225_ = 1usize;
    v___x_3226_ = lean_usize_sub(v___x_3224_, v___x_3225_);
    v___x_3227_ = lean_usize_land(v___x_3223_, v___x_3226_);
    v___x_3228_ = lean_array_uget_borrowed(v_buckets_3214_, v___x_3227_);
    v___x_3229_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_3213_, v___x_3228_);
    return v___x_3229_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg___boxed(
    mut v_m_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_3230_, v_a_3231_);
    crate::leanh::lean_dec_ref(v_a_3231_);
    crate::leanh::lean_dec_ref(v_m_3230_);
    return v_res_3232_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(
    mut v_x_3233_: *mut crate::leanh::LeanObject,
    mut v_x_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: u64 = 0;
    let mut v___x_3243_: u64 = 0;
    let mut v___x_3244_: u64 = 0;
    let mut v_fold_3245_: u64 = 0;
    let mut v___x_3246_: u64 = 0;
    let mut v___x_3247_: u64 = 0;
    let mut v___x_3248_: u64 = 0;
    let mut v___x_3249_: usize = 0;
    let mut v___x_3250_: usize = 0;
    let mut v___x_3251_: usize = 0;
    let mut v___x_3252_: usize = 0;
    let mut v___x_3253_: usize = 0;
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3234_) == 0 {
                    return v_x_3233_;
                } else {
                    v_key_3235_ = crate::leanh::lean_ctor_get(v_x_3234_, 0);
                    v_value_3236_ = crate::leanh::lean_ctor_get(v_x_3234_, 1);
                    v_tail_3237_ = crate::leanh::lean_ctor_get(v_x_3234_, 2);
                    v_isSharedCheck_3260_ = (!crate::leanh::lean_is_exclusive(v_x_3234_)) as u8;
                    if v_isSharedCheck_3260_ == 0 {
                        v___x_3239_ = v_x_3234_;
                        v_isShared_3240_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3237_);
                        crate::leanh::lean_inc(v_value_3236_);
                        crate::leanh::lean_inc(v_key_3235_);
                        crate::leanh::lean_dec(v_x_3234_);
                        v___x_3239_ = crate::leanh::lean_box(0);
                        v_isShared_3240_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3241_ = lean_array_get_size(v_x_3233_);
                v___x_3242_ = l_Lean_Expr_hash(v_key_3235_);
                v___x_3243_ = 32u64;
                v___x_3244_ = lean_uint64_shift_right(v___x_3242_, v___x_3243_);
                v_fold_3245_ = lean_uint64_xor(v___x_3242_, v___x_3244_);
                v___x_3246_ = 16u64;
                v___x_3247_ = lean_uint64_shift_right(v_fold_3245_, v___x_3246_);
                v___x_3248_ = lean_uint64_xor(v_fold_3245_, v___x_3247_);
                v___x_3249_ = lean_uint64_to_usize(v___x_3248_);
                v___x_3250_ = lean_usize_of_nat(v___x_3241_);
                v___x_3251_ = 1usize;
                v___x_3252_ = lean_usize_sub(v___x_3250_, v___x_3251_);
                v___x_3253_ = lean_usize_land(v___x_3249_, v___x_3252_);
                v___x_3254_ = lean_array_uget_borrowed(v_x_3233_, v___x_3253_);
                crate::leanh::lean_inc(v___x_3254_);
                if v_isShared_3240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3239_, 2, v___x_3254_);
                    v___x_3256_ = v___x_3239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_key_3235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_value_3236_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 2, v___x_3254_);
                    v___x_3256_ = v_reuseFailAlloc_3259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3257_ = lean_array_uset(v_x_3233_, v___x_3253_, v___x_3256_);
                v_x_3233_ = v___x_3257_;
                v_x_3234_ = v_tail_3237_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(
    mut v_i_3261_: *mut crate::leanh::LeanObject,
    mut v_source_3262_: *mut crate::leanh::LeanObject,
    mut v_target_3263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: u8 = 0;
    let mut v_es_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3264_ = lean_array_get_size(v_source_3262_);
                v___x_3265_ = lean_nat_dec_lt(v_i_3261_, v___x_3264_);
                if v___x_3265_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3262_);
                    crate::leanh::lean_dec(v_i_3261_);
                    return v_target_3263_;
                } else {
                    v_es_3266_ = lean_array_fget(v_source_3262_, v_i_3261_);
                    v___x_3267_ = crate::leanh::lean_box(0);
                    v_source_3268_ = lean_array_fset(v_source_3262_, v_i_3261_, v___x_3267_);
                    v_target_3269_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_target_3263_, v_es_3266_);
                    v___x_3270_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3271_ = lean_nat_add(v_i_3261_, v___x_3270_);
                    crate::leanh::lean_dec(v_i_3261_);
                    v_i_3261_ = v___x_3271_;
                    v_source_3262_ = v_source_3268_;
                    v_target_3263_ = v_target_3269_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(
    mut v_data_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = lean_array_get_size(v_data_3273_);
    v___x_3275_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3276_ = lean_nat_mul(v___x_3274_, v___x_3275_);
    v___x_3277_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3278_ = crate::leanh::lean_box(0);
    v___x_3279_ = lean_mk_array(v_nbuckets_3276_, v___x_3278_);
    v___x_3280_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v___x_3277_, v_data_3273_, v___x_3279_);
    return v___x_3280_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(
    mut v_a_3281_: *mut crate::leanh::LeanObject,
    mut v_b_3282_: *mut crate::leanh::LeanObject,
    mut v_x_3283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3289_: u8 = 0;
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3283_) == 0 {
                    crate::leanh::lean_dec(v_b_3282_);
                    crate::leanh::lean_dec_ref(v_a_3281_);
                    return v_x_3283_;
                } else {
                    v_key_3284_ = crate::leanh::lean_ctor_get(v_x_3283_, 0);
                    v_value_3285_ = crate::leanh::lean_ctor_get(v_x_3283_, 1);
                    v_tail_3286_ = crate::leanh::lean_ctor_get(v_x_3283_, 2);
                    v_isSharedCheck_3298_ = (!crate::leanh::lean_is_exclusive(v_x_3283_)) as u8;
                    if v_isSharedCheck_3298_ == 0 {
                        v___x_3288_ = v_x_3283_;
                        v_isShared_3289_ = v_isSharedCheck_3298_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3286_);
                        crate::leanh::lean_inc(v_value_3285_);
                        crate::leanh::lean_inc(v_key_3284_);
                        crate::leanh::lean_dec(v_x_3283_);
                        v___x_3288_ = crate::leanh::lean_box(0);
                        v_isShared_3289_ = v_isSharedCheck_3298_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3290_ = lean_expr_eqv(v_key_3284_, v_a_3281_);
                if v___x_3290_ == 0 {
                    v___x_3291_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_3281_, v_b_3282_, v_tail_3286_);
                    if v_isShared_3289_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3288_, 2, v___x_3291_);
                        v___x_3293_ = v___x_3288_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3294_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_key_3284_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_value_3285_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 2, v___x_3291_);
                        v___x_3293_ = v_reuseFailAlloc_3294_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3285_);
                    crate::leanh::lean_dec(v_key_3284_);
                    if v_isShared_3289_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3288_, 1, v_b_3282_);
                        crate::leanh::lean_ctor_set(v___x_3288_, 0, v_a_3281_);
                        v___x_3296_ = v___x_3288_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3297_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3281_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_b_3282_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_tail_3286_);
                        v___x_3296_ = v_reuseFailAlloc_3297_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3293_;
            }
            3 => {
                return v___x_3296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_x_3300_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3301_: u8 = 0;
    let mut v_key_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3300_) == 0 {
                    v___x_3301_ = 0;
                    return v___x_3301_;
                } else {
                    v_key_3302_ = crate::leanh::lean_ctor_get(v_x_3300_, 0);
                    v_tail_3303_ = crate::leanh::lean_ctor_get(v_x_3300_, 2);
                    v___x_3304_ = lean_expr_eqv(v_key_3302_, v_a_3299_);
                    if v___x_3304_ == 0 {
                        v_x_3300_ = v_tail_3303_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3304_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg___boxed(
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_x_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3308_: u8 = 0;
    let mut v_r_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3308_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_3306_, v_x_3307_);
    crate::leanh::lean_dec(v_x_3307_);
    crate::leanh::lean_dec_ref(v_a_3306_);
    v_r_3309_ = crate::leanh::lean_box((v_res_3308_) as usize);
    return v_r_3309_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(
    mut v_m_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_b_3312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: u64 = 0;
    let mut v___x_3320_: u64 = 0;
    let mut v___x_3321_: u64 = 0;
    let mut v_fold_3322_: u64 = 0;
    let mut v___x_3323_: u64 = 0;
    let mut v___x_3324_: u64 = 0;
    let mut v___x_3325_: u64 = 0;
    let mut v___x_3326_: usize = 0;
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: usize = 0;
    let mut v___x_3329_: usize = 0;
    let mut v___x_3330_: usize = 0;
    let mut v_bkt_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: u8 = 0;
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut v_val_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3313_ = crate::leanh::lean_ctor_get(v_m_3310_, 0);
                v_buckets_3314_ = crate::leanh::lean_ctor_get(v_m_3310_, 1);
                v_isSharedCheck_3357_ = (!crate::leanh::lean_is_exclusive(v_m_3310_)) as u8;
                if v_isSharedCheck_3357_ == 0 {
                    v___x_3316_ = v_m_3310_;
                    v_isShared_3317_ = v_isSharedCheck_3357_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3314_);
                    crate::leanh::lean_inc(v_size_3313_);
                    crate::leanh::lean_dec(v_m_3310_);
                    v___x_3316_ = crate::leanh::lean_box(0);
                    v_isShared_3317_ = v_isSharedCheck_3357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3318_ = lean_array_get_size(v_buckets_3314_);
                v___x_3319_ = l_Lean_Expr_hash(v_a_3311_);
                v___x_3320_ = 32u64;
                v___x_3321_ = lean_uint64_shift_right(v___x_3319_, v___x_3320_);
                v_fold_3322_ = lean_uint64_xor(v___x_3319_, v___x_3321_);
                v___x_3323_ = 16u64;
                v___x_3324_ = lean_uint64_shift_right(v_fold_3322_, v___x_3323_);
                v___x_3325_ = lean_uint64_xor(v_fold_3322_, v___x_3324_);
                v___x_3326_ = lean_uint64_to_usize(v___x_3325_);
                v___x_3327_ = lean_usize_of_nat(v___x_3318_);
                v___x_3328_ = 1usize;
                v___x_3329_ = lean_usize_sub(v___x_3327_, v___x_3328_);
                v___x_3330_ = lean_usize_land(v___x_3326_, v___x_3329_);
                v_bkt_3331_ = lean_array_uget_borrowed(v_buckets_3314_, v___x_3330_);
                v___x_3332_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_3311_, v_bkt_3331_);
                if v___x_3332_ == 0 {
                    v___x_3333_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3334_ = lean_nat_add(v_size_3313_, v___x_3333_);
                    crate::leanh::lean_dec(v_size_3313_);
                    crate::leanh::lean_inc(v_bkt_3331_);
                    v___x_3335_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v_a_3311_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_b_3312_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_bkt_3331_);
                    v_buckets_x27_3336_ =
                        lean_array_uset(v_buckets_3314_, v___x_3330_, v___x_3335_);
                    v___x_3337_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3338_ = lean_nat_mul(v_size_x27_3334_, v___x_3337_);
                    v___x_3339_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3340_ = lean_nat_div(v___x_3338_, v___x_3339_);
                    crate::leanh::lean_dec(v___x_3338_);
                    v___x_3341_ = lean_array_get_size(v_buckets_x27_3336_);
                    v___x_3342_ = lean_nat_dec_le(v___x_3340_, v___x_3341_);
                    crate::leanh::lean_dec(v___x_3340_);
                    if v___x_3342_ == 0 {
                        v_val_3343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_buckets_x27_3336_);
                        if v_isShared_3317_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3316_, 1, v_val_3343_);
                            crate::leanh::lean_ctor_set(v___x_3316_, 0, v_size_x27_3334_);
                            v___x_3345_ = v___x_3316_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3346_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3346_,
                                0,
                                v_size_x27_3334_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_val_3343_);
                            v___x_3345_ = v_reuseFailAlloc_3346_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3317_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3316_, 1, v_buckets_x27_3336_);
                            crate::leanh::lean_ctor_set(v___x_3316_, 0, v_size_x27_3334_);
                            v___x_3348_ = v___x_3316_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3349_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3349_,
                                0,
                                v_size_x27_3334_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3349_,
                                1,
                                v_buckets_x27_3336_,
                            );
                            v___x_3348_ = v_reuseFailAlloc_3349_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3331_);
                    v___x_3350_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3351_ =
                        lean_array_uset(v_buckets_3314_, v___x_3330_, v___x_3350_);
                    v___x_3352_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_3311_, v_b_3312_, v_bkt_3331_);
                    v___x_3353_ = lean_array_uset(v_buckets_x27_3351_, v___x_3330_, v___x_3352_);
                    if v_isShared_3317_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3316_, 1, v___x_3353_);
                        v___x_3355_ = v___x_3316_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_size_3313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3353_);
                        v___x_3355_ = v_reuseFailAlloc_3356_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3345_;
            }
            3 => {
                return v___x_3348_;
            }
            4 => {
                return v___x_3355_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(
    mut v___x_3358_: *mut crate::leanh::LeanObject,
    mut v___x_3359_: *mut crate::leanh::LeanObject,
    mut v_fst_3360_: *mut crate::leanh::LeanObject,
    mut v_fproof_3361_: *mut crate::leanh::LeanObject,
    mut v_snd_3362_: *mut crate::leanh::LeanObject,
    mut v_sproof_3363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v_val_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_val_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_fproof_3361_) == 0 {
                    crate::leanh::lean_dec_ref(v_snd_3362_);
                    crate::leanh::lean_dec(v___x_3359_);
                    if crate::leanh::lean_obj_tag(v_sproof_3363_) == 0 {
                        crate::leanh::lean_dec_ref(v_fst_3360_);
                        crate::leanh::lean_dec(v___x_3358_);
                        v___x_3364_ = crate::leanh::lean_box(0);
                        return v___x_3364_;
                    } else {
                        v_val_3365_ = crate::leanh::lean_ctor_get(v_sproof_3363_, 0);
                        v_isSharedCheck_3374_ =
                            (!crate::leanh::lean_is_exclusive(v_sproof_3363_)) as u8;
                        if v_isSharedCheck_3374_ == 0 {
                            v___x_3367_ = v_sproof_3363_;
                            v_isShared_3368_ = v_isSharedCheck_3374_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3365_);
                            crate::leanh::lean_dec(v_sproof_3363_);
                            v___x_3367_ = crate::leanh::lean_box(0);
                            v_isShared_3368_ = v_isSharedCheck_3374_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fst_3360_);
                    crate::leanh::lean_dec(v___x_3358_);
                    if crate::leanh::lean_obj_tag(v_sproof_3363_) == 0 {
                        v_val_3375_ = crate::leanh::lean_ctor_get(v_fproof_3361_, 0);
                        v_isSharedCheck_3384_ =
                            (!crate::leanh::lean_is_exclusive(v_fproof_3361_)) as u8;
                        if v_isSharedCheck_3384_ == 0 {
                            v___x_3377_ = v_fproof_3361_;
                            v_isShared_3378_ = v_isSharedCheck_3384_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3375_);
                            crate::leanh::lean_dec(v_fproof_3361_);
                            v___x_3377_ = crate::leanh::lean_box(0);
                            v_isShared_3378_ = v_isSharedCheck_3384_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_snd_3362_);
                        crate::leanh::lean_dec(v___x_3359_);
                        v_val_3385_ = crate::leanh::lean_ctor_get(v_fproof_3361_, 0);
                        crate::leanh::lean_inc(v_val_3385_);
                        crate::leanh::lean_dec_ref_known(v_fproof_3361_, 1);
                        v_val_3386_ = crate::leanh::lean_ctor_get(v_sproof_3363_, 0);
                        v_isSharedCheck_3394_ =
                            (!crate::leanh::lean_is_exclusive(v_sproof_3363_)) as u8;
                        if v_isSharedCheck_3394_ == 0 {
                            v___x_3388_ = v_sproof_3363_;
                            v_isShared_3389_ = v_isSharedCheck_3394_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3386_);
                            crate::leanh::lean_dec(v_sproof_3363_);
                            v___x_3388_ = crate::leanh::lean_box(0);
                            v_isShared_3389_ = v_isSharedCheck_3394_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3369_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_3358_, v_fst_3360_);
                v___x_3370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3370_, 0, v___x_3369_);
                crate::leanh::lean_ctor_set(v___x_3370_, 1, v_val_3365_);
                if v_isShared_3368_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3367_, 0, v___x_3370_);
                    v___x_3372_ = v___x_3367_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
                    v___x_3372_ = v_reuseFailAlloc_3373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3372_;
            }
            3 => {
                v___x_3379_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_3359_, v_snd_3362_);
                v___x_3380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3380_, 0, v_val_3375_);
                crate::leanh::lean_ctor_set(v___x_3380_, 1, v___x_3379_);
                if v_isShared_3378_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3377_, 0, v___x_3380_);
                    v___x_3382_ = v___x_3377_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3382_;
            }
            5 => {
                v___x_3390_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3390_, 0, v_val_3385_);
                crate::leanh::lean_ctor_set(v___x_3390_, 1, v_val_3386_);
                if v_isShared_3389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3388_, 0, v___x_3390_);
                    v___x_3392_ = v___x_3388_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
                    v___x_3392_ = v_reuseFailAlloc_3393_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3392_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0(
    mut v_width_3397_: *mut crate::leanh::LeanObject,
    mut v_expr_3398_: *mut crate::leanh::LeanObject,
    mut v_width_3399_: *mut crate::leanh::LeanObject,
    mut v_expr_3400_: *mut crate::leanh::LeanObject,
    mut v_val_3401_: *mut crate::leanh::LeanObject,
    mut v_val_3402_: *mut crate::leanh::LeanObject,
    mut v___x_3403_: *mut crate::leanh::LeanObject,
    mut v___x_3404_: *mut crate::leanh::LeanObject,
    mut v___x_3405_: *mut crate::leanh::LeanObject,
    mut v___x_3406_: *mut crate::leanh::LeanObject,
    mut v___x_3407_: *mut crate::leanh::LeanObject,
    mut v___x_3408_: *mut crate::leanh::LeanObject,
    mut v___x_3409_: *mut crate::leanh::LeanObject,
    mut v_arg_3410_: *mut crate::leanh::LeanObject,
    mut v_arg_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v_fst_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut v_a_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3456_: u8 = 0;
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut v_a_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_width_3397_);
                v___x_3418_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3397_,
                    v_expr_3398_,
                    v___y_3412_,
                    v___y_3413_,
                    v___y_3414_,
                    v___y_3415_,
                    v___y_3416_,
                );
                if crate::leanh::lean_obj_tag(v___x_3418_) == 0 {
                    v_a_3419_ = crate::leanh::lean_ctor_get(v___x_3418_, 0);
                    crate::leanh::lean_inc(v_a_3419_);
                    crate::leanh::lean_dec_ref_known(v___x_3418_, 1);
                    crate::leanh::lean_inc(v_width_3399_);
                    v___x_3420_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                        v_width_3399_,
                        v_expr_3400_,
                        v___y_3412_,
                        v___y_3413_,
                        v___y_3414_,
                        v___y_3415_,
                        v___y_3416_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3420_) == 0 {
                        v_a_3421_ = crate::leanh::lean_ctor_get(v___x_3420_, 0);
                        crate::leanh::lean_inc(v_a_3421_);
                        crate::leanh::lean_dec_ref_known(v___x_3420_, 1);
                        v___x_3422_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                            v_val_3401_,
                            v___y_3412_,
                            v___y_3413_,
                            v___y_3414_,
                            v___y_3415_,
                            v___y_3416_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3422_) == 0 {
                            v_a_3423_ = crate::leanh::lean_ctor_get(v___x_3422_, 0);
                            crate::leanh::lean_inc(v_a_3423_);
                            crate::leanh::lean_dec_ref_known(v___x_3422_, 1);
                            v___x_3424_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                                v_val_3402_,
                                v___y_3412_,
                                v___y_3413_,
                                v___y_3414_,
                                v___y_3415_,
                                v___y_3416_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3424_) == 0 {
                                v_a_3425_ = crate::leanh::lean_ctor_get(v___x_3424_, 0);
                                v_isSharedCheck_3452_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3424_)) as u8;
                                if v_isSharedCheck_3452_ == 0 {
                                    v___x_3427_ = v___x_3424_;
                                    v_isShared_3428_ = v_isSharedCheck_3452_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3425_);
                                    crate::leanh::lean_dec(v___x_3424_);
                                    v___x_3427_ = crate::leanh::lean_box(0);
                                    v_isShared_3428_ = v_isSharedCheck_3452_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3423_);
                                crate::leanh::lean_dec(v_a_3421_);
                                crate::leanh::lean_dec(v_a_3419_);
                                crate::leanh::lean_dec_ref(v_arg_3411_);
                                crate::leanh::lean_dec_ref(v_arg_3410_);
                                crate::leanh::lean_dec_ref(v___x_3409_);
                                crate::leanh::lean_dec_ref(v___x_3408_);
                                crate::leanh::lean_dec(v___x_3407_);
                                crate::leanh::lean_dec_ref(v___x_3406_);
                                crate::leanh::lean_dec_ref(v___x_3405_);
                                crate::leanh::lean_dec_ref(v___x_3404_);
                                crate::leanh::lean_dec_ref(v___x_3403_);
                                crate::leanh::lean_dec(v_width_3399_);
                                crate::leanh::lean_dec(v_width_3397_);
                                return v___x_3424_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3421_);
                            crate::leanh::lean_dec(v_a_3419_);
                            crate::leanh::lean_dec_ref(v_arg_3411_);
                            crate::leanh::lean_dec_ref(v_arg_3410_);
                            crate::leanh::lean_dec_ref(v___x_3409_);
                            crate::leanh::lean_dec_ref(v___x_3408_);
                            crate::leanh::lean_dec(v___x_3407_);
                            crate::leanh::lean_dec_ref(v___x_3406_);
                            crate::leanh::lean_dec_ref(v___x_3405_);
                            crate::leanh::lean_dec_ref(v___x_3404_);
                            crate::leanh::lean_dec_ref(v___x_3403_);
                            crate::leanh::lean_dec_ref(v_val_3402_);
                            crate::leanh::lean_dec(v_width_3399_);
                            crate::leanh::lean_dec(v_width_3397_);
                            return v___x_3422_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3419_);
                        crate::leanh::lean_dec_ref(v_arg_3411_);
                        crate::leanh::lean_dec_ref(v_arg_3410_);
                        crate::leanh::lean_dec_ref(v___x_3409_);
                        crate::leanh::lean_dec_ref(v___x_3408_);
                        crate::leanh::lean_dec(v___x_3407_);
                        crate::leanh::lean_dec_ref(v___x_3406_);
                        crate::leanh::lean_dec_ref(v___x_3405_);
                        crate::leanh::lean_dec_ref(v___x_3404_);
                        crate::leanh::lean_dec_ref(v___x_3403_);
                        crate::leanh::lean_dec_ref(v_val_3402_);
                        crate::leanh::lean_dec_ref(v_val_3401_);
                        crate::leanh::lean_dec(v_width_3399_);
                        crate::leanh::lean_dec(v_width_3397_);
                        v_a_3453_ = crate::leanh::lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3460_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3460_ == 0 {
                            v___x_3455_ = v___x_3420_;
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3453_);
                            crate::leanh::lean_dec(v___x_3420_);
                            v___x_3455_ = crate::leanh::lean_box(0);
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_3411_);
                    crate::leanh::lean_dec_ref(v_arg_3410_);
                    crate::leanh::lean_dec_ref(v___x_3409_);
                    crate::leanh::lean_dec_ref(v___x_3408_);
                    crate::leanh::lean_dec(v___x_3407_);
                    crate::leanh::lean_dec_ref(v___x_3406_);
                    crate::leanh::lean_dec_ref(v___x_3405_);
                    crate::leanh::lean_dec_ref(v___x_3404_);
                    crate::leanh::lean_dec_ref(v___x_3403_);
                    crate::leanh::lean_dec_ref(v_val_3402_);
                    crate::leanh::lean_dec_ref(v_val_3401_);
                    crate::leanh::lean_dec_ref(v_expr_3400_);
                    crate::leanh::lean_dec(v_width_3399_);
                    crate::leanh::lean_dec(v_width_3397_);
                    v_a_3461_ = crate::leanh::lean_ctor_get(v___x_3418_, 0);
                    v_isSharedCheck_3468_ = (!crate::leanh::lean_is_exclusive(v___x_3418_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3463_ = v___x_3418_;
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3461_);
                        crate::leanh::lean_dec(v___x_3418_);
                        v___x_3463_ = crate::leanh::lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_3421_);
                crate::leanh::lean_inc(v_a_3419_);
                v___x_3429_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(v_width_3397_, v_width_3399_, v_a_3419_, v_a_3423_, v_a_3421_, v_a_3425_);
                if crate::leanh::lean_obj_tag(v___x_3429_) == 1 {
                    v_val_3430_ = crate::leanh::lean_ctor_get(v___x_3429_, 0);
                    v_isSharedCheck_3447_ = (!crate::leanh::lean_is_exclusive(v___x_3429_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v___x_3432_ = v___x_3429_;
                        v_isShared_3433_ = v_isSharedCheck_3447_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3430_);
                        crate::leanh::lean_dec(v___x_3429_);
                        v___x_3432_ = crate::leanh::lean_box(0);
                        v_isShared_3433_ = v_isSharedCheck_3447_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3429_);
                    crate::leanh::lean_dec(v_a_3421_);
                    crate::leanh::lean_dec(v_a_3419_);
                    crate::leanh::lean_dec_ref(v_arg_3411_);
                    crate::leanh::lean_dec_ref(v_arg_3410_);
                    crate::leanh::lean_dec_ref(v___x_3409_);
                    crate::leanh::lean_dec_ref(v___x_3408_);
                    crate::leanh::lean_dec(v___x_3407_);
                    crate::leanh::lean_dec_ref(v___x_3406_);
                    crate::leanh::lean_dec_ref(v___x_3405_);
                    crate::leanh::lean_dec_ref(v___x_3404_);
                    crate::leanh::lean_dec_ref(v___x_3403_);
                    v___x_3448_ = crate::leanh::lean_box(0);
                    if v_isShared_3428_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3427_, 0, v___x_3448_);
                        v___x_3450_ = v___x_3427_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
                        v___x_3450_ = v_reuseFailAlloc_3451_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3434_ = crate::leanh::lean_ctor_get(v_val_3430_, 0);
                crate::leanh::lean_inc(v_fst_3434_);
                v_snd_3435_ = crate::leanh::lean_ctor_get(v_val_3430_, 1);
                crate::leanh::lean_inc(v_snd_3435_);
                crate::leanh::lean_dec(v_val_3430_);
                v___x_3436_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0;
                v___x_3437_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__1;
                v___x_3438_ = l_Lean_Name_mkStr6(
                    v___x_3403_,
                    v___x_3404_,
                    v___x_3405_,
                    v___x_3436_,
                    v___x_3406_,
                    v___x_3437_,
                );
                v___x_3439_ = l_Lean_mkConst(v___x_3438_, v___x_3407_);
                v___x_3440_ = l_Lean_mkApp8(
                    v___x_3439_,
                    v___x_3408_,
                    v___x_3409_,
                    v_arg_3410_,
                    v_a_3419_,
                    v_arg_3411_,
                    v_a_3421_,
                    v_fst_3434_,
                    v_snd_3435_,
                );
                if v_isShared_3433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3432_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3432_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3440_);
                    v___x_3442_ = v_reuseFailAlloc_3446_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3428_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3427_, 0, v___x_3442_);
                    v___x_3444_ = v___x_3427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3444_;
            }
            5 => {
                return v___x_3450_;
            }
            6 => {
                if v_isShared_3456_ == 0 {
                    v___x_3458_ = v___x_3455_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
                    v___x_3458_ = v_reuseFailAlloc_3459_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3458_;
            }
            8 => {
                if v_isShared_3464_ == 0 {
                    v___x_3466_ = v___x_3463_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
                    v___x_3466_ = v_reuseFailAlloc_3467_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_width_3469_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_expr_3470_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_width_3471_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_expr_3472_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_val_3473_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_val_3474_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3475_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3476_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_3477_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_3478_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_3479_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_3480_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_3481_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_arg_3482_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_arg_3483_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3484_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3485_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3486_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_3487_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3488_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_3489_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3490_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0(v_width_3469_, v_expr_3470_, v_width_3471_, v_expr_3472_, v_val_3473_, v_val_3474_, v___x_3475_, v___x_3476_, v___x_3477_, v___x_3478_, v___x_3479_, v___x_3480_, v___x_3481_, v_arg_3482_, v_arg_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
    crate::leanh::lean_dec(v___y_3488_);
    crate::leanh::lean_dec_ref(v___y_3487_);
    crate::leanh::lean_dec(v___y_3486_);
    crate::leanh::lean_dec_ref(v___y_3485_);
    crate::leanh::lean_dec(v___y_3484_);
    return v_res_3490_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(
    mut v_n_3491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3492_, 0, v_n_3491_);
    return v___x_3492_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(
    mut v_n_3493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3494_, 0, v_n_3493_);
    return v___x_3494_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(
    mut v_msgData_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3501_ = lean_st_ref_get(v___y_3499_);
    v_env_3502_ = crate::leanh::lean_ctor_get(v___x_3501_, 0);
    crate::leanh::lean_inc_ref(v_env_3502_);
    crate::leanh::lean_dec(v___x_3501_);
    v___x_3503_ = lean_st_ref_get(v___y_3497_);
    v_mctx_3504_ = crate::leanh::lean_ctor_get(v___x_3503_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3504_);
    crate::leanh::lean_dec(v___x_3503_);
    v_lctx_3505_ = crate::leanh::lean_ctor_get(v___y_3496_, 2);
    v_options_3506_ = crate::leanh::lean_ctor_get(v___y_3498_, 2);
    crate::leanh::lean_inc_ref(v_options_3506_);
    crate::leanh::lean_inc_ref(v_lctx_3505_);
    v___x_3507_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3507_, 0, v_env_3502_);
    crate::leanh::lean_ctor_set(v___x_3507_, 1, v_mctx_3504_);
    crate::leanh::lean_ctor_set(v___x_3507_, 2, v_lctx_3505_);
    crate::leanh::lean_ctor_set(v___x_3507_, 3, v_options_3506_);
    v___x_3508_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3507_);
    crate::leanh::lean_ctor_set(v___x_3508_, 1, v_msgData_3495_);
    v___x_3509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3509_, 0, v___x_3508_);
    return v___x_3509_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(
    mut v_msgData_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3516_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(v_msgData_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
    crate::leanh::lean_dec(v___y_3514_);
    crate::leanh::lean_dec_ref(v___y_3513_);
    crate::leanh::lean_dec(v___y_3512_);
    crate::leanh::lean_dec_ref(v___y_3511_);
    return v_res_3516_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(
    mut v_msg_3517_: *mut crate::leanh::LeanObject,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
    mut v___y_3520_: *mut crate::leanh::LeanObject,
    mut v___y_3521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3523_ = crate::leanh::lean_ctor_get(v___y_3520_, 5);
                v___x_3524_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(v_msg_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
                v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                v_isSharedCheck_3533_ = (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                if v_isSharedCheck_3533_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3525_);
                    crate::leanh::lean_dec(v___x_3524_);
                    v___x_3527_ = crate::leanh::lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3523_);
                v___x_3529_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3529_, 0, v_ref_3523_);
                crate::leanh::lean_ctor_set(v___x_3529_, 1, v_a_3525_);
                if v_isShared_3528_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3527_, 1);
                    crate::leanh::lean_ctor_set(v___x_3527_, 0, v___x_3529_);
                    v___x_3531_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
                    v___x_3531_ = v_reuseFailAlloc_3532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg___boxed(
    mut v_msg_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3540_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
    crate::leanh::lean_dec(v___y_3538_);
    crate::leanh::lean_dec_ref(v___y_3537_);
    crate::leanh::lean_dec(v___y_3536_);
    crate::leanh::lean_dec_ref(v___y_3535_);
    return v_res_3540_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(
    mut v_width_3542_: *mut crate::leanh::LeanObject,
    mut v_expr_3543_: *mut crate::leanh::LeanObject,
    mut v_val_3544_: *mut crate::leanh::LeanObject,
    mut v___x_3545_: *mut crate::leanh::LeanObject,
    mut v___x_3546_: *mut crate::leanh::LeanObject,
    mut v___x_3547_: *mut crate::leanh::LeanObject,
    mut v___x_3548_: *mut crate::leanh::LeanObject,
    mut v___x_3549_: *mut crate::leanh::LeanObject,
    mut v___x_3550_: *mut crate::leanh::LeanObject,
    mut v___x_3551_: *mut crate::leanh::LeanObject,
    mut v_arg_3552_: *mut crate::leanh::LeanObject,
    mut v___y_3553_: *mut crate::leanh::LeanObject,
    mut v___y_3554_: *mut crate::leanh::LeanObject,
    mut v___y_3555_: *mut crate::leanh::LeanObject,
    mut v___y_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v_val_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut v_a_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3559_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3542_,
                    v_expr_3543_,
                    v___y_3553_,
                    v___y_3554_,
                    v___y_3555_,
                    v___y_3556_,
                    v___y_3557_,
                );
                if crate::leanh::lean_obj_tag(v___x_3559_) == 0 {
                    v_a_3560_ = crate::leanh::lean_ctor_get(v___x_3559_, 0);
                    crate::leanh::lean_inc(v_a_3560_);
                    crate::leanh::lean_dec_ref_known(v___x_3559_, 1);
                    v___x_3561_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                        v_val_3544_,
                        v___y_3553_,
                        v___y_3554_,
                        v___y_3555_,
                        v___y_3556_,
                        v___y_3557_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3561_) == 0 {
                        v_a_3562_ = crate::leanh::lean_ctor_get(v___x_3561_, 0);
                        v_isSharedCheck_3586_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3561_)) as u8;
                        if v_isSharedCheck_3586_ == 0 {
                            v___x_3564_ = v___x_3561_;
                            v_isShared_3565_ = v_isSharedCheck_3586_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3562_);
                            crate::leanh::lean_dec(v___x_3561_);
                            v___x_3564_ = crate::leanh::lean_box(0);
                            v_isShared_3565_ = v_isSharedCheck_3586_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3560_);
                        crate::leanh::lean_dec_ref(v_arg_3552_);
                        crate::leanh::lean_dec_ref(v___x_3551_);
                        crate::leanh::lean_dec_ref(v___x_3550_);
                        crate::leanh::lean_dec(v___x_3549_);
                        crate::leanh::lean_dec_ref(v___x_3548_);
                        crate::leanh::lean_dec_ref(v___x_3547_);
                        crate::leanh::lean_dec_ref(v___x_3546_);
                        crate::leanh::lean_dec_ref(v___x_3545_);
                        return v___x_3561_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_3552_);
                    crate::leanh::lean_dec_ref(v___x_3551_);
                    crate::leanh::lean_dec_ref(v___x_3550_);
                    crate::leanh::lean_dec(v___x_3549_);
                    crate::leanh::lean_dec_ref(v___x_3548_);
                    crate::leanh::lean_dec_ref(v___x_3547_);
                    crate::leanh::lean_dec_ref(v___x_3546_);
                    crate::leanh::lean_dec_ref(v___x_3545_);
                    crate::leanh::lean_dec_ref(v_val_3544_);
                    v_a_3587_ = crate::leanh::lean_ctor_get(v___x_3559_, 0);
                    v_isSharedCheck_3594_ = (!crate::leanh::lean_is_exclusive(v___x_3559_)) as u8;
                    if v_isSharedCheck_3594_ == 0 {
                        v___x_3589_ = v___x_3559_;
                        v_isShared_3590_ = v_isSharedCheck_3594_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3587_);
                        crate::leanh::lean_dec(v___x_3559_);
                        v___x_3589_ = crate::leanh::lean_box(0);
                        v_isShared_3590_ = v_isSharedCheck_3594_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3562_) == 1 {
                    v_val_3566_ = crate::leanh::lean_ctor_get(v_a_3562_, 0);
                    v_isSharedCheck_3581_ = (!crate::leanh::lean_is_exclusive(v_a_3562_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3568_ = v_a_3562_;
                        v_isShared_3569_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3566_);
                        crate::leanh::lean_dec(v_a_3562_);
                        v___x_3568_ = crate::leanh::lean_box(0);
                        v_isShared_3569_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3562_);
                    crate::leanh::lean_dec(v_a_3560_);
                    crate::leanh::lean_dec_ref(v_arg_3552_);
                    crate::leanh::lean_dec_ref(v___x_3551_);
                    crate::leanh::lean_dec_ref(v___x_3550_);
                    crate::leanh::lean_dec(v___x_3549_);
                    crate::leanh::lean_dec_ref(v___x_3548_);
                    crate::leanh::lean_dec_ref(v___x_3547_);
                    crate::leanh::lean_dec_ref(v___x_3546_);
                    crate::leanh::lean_dec_ref(v___x_3545_);
                    v___x_3582_ = crate::leanh::lean_box(0);
                    if v_isShared_3565_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3564_, 0, v___x_3582_);
                        v___x_3584_ = v___x_3564_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
                        v___x_3584_ = v_reuseFailAlloc_3585_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3570_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0;
                v___x_3571_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0;
                v___x_3572_ = l_Lean_Name_mkStr6(
                    v___x_3545_,
                    v___x_3546_,
                    v___x_3547_,
                    v___x_3570_,
                    v___x_3548_,
                    v___x_3571_,
                );
                v___x_3573_ = l_Lean_mkConst(v___x_3572_, v___x_3549_);
                v___x_3574_ = l_Lean_mkApp5(
                    v___x_3573_,
                    v___x_3550_,
                    v___x_3551_,
                    v_arg_3552_,
                    v_a_3560_,
                    v_val_3566_,
                );
                if v_isShared_3569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3568_, 0, v___x_3574_);
                    v___x_3576_ = v___x_3568_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3574_);
                    v___x_3576_ = v_reuseFailAlloc_3580_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3565_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3564_, 0, v___x_3576_);
                    v___x_3578_ = v___x_3564_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
                    v___x_3578_ = v_reuseFailAlloc_3579_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3578_;
            }
            5 => {
                return v___x_3584_;
            }
            6 => {
                if v_isShared_3590_ == 0 {
                    v___x_3592_ = v___x_3589_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3593_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
                    v___x_3592_ = v_reuseFailAlloc_3593_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_width_3595_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_expr_3596_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_val_3597_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3598_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3599_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3600_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3601_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3602_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_3603_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_3604_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_arg_3605_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3606_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3607_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3608_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3609_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3610_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3611_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(v_width_3595_, v_expr_3596_, v_val_3597_, v___x_3598_, v___x_3599_, v___x_3600_, v___x_3601_, v___x_3602_, v___x_3603_, v___x_3604_, v_arg_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
    crate::leanh::lean_dec(v___y_3610_);
    crate::leanh::lean_dec_ref(v___y_3609_);
    crate::leanh::lean_dec(v___y_3608_);
    crate::leanh::lean_dec_ref(v___y_3607_);
    crate::leanh::lean_dec(v___y_3606_);
    return v_res_3612_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(
    mut v_width_3614_: *mut crate::leanh::LeanObject,
    mut v_expr_3615_: *mut crate::leanh::LeanObject,
    mut v_val_3616_: *mut crate::leanh::LeanObject,
    mut v___x_3617_: *mut crate::leanh::LeanObject,
    mut v___x_3618_: *mut crate::leanh::LeanObject,
    mut v___x_3619_: *mut crate::leanh::LeanObject,
    mut v___x_3620_: *mut crate::leanh::LeanObject,
    mut v___x_3621_: *mut crate::leanh::LeanObject,
    mut v_arg_3622_: *mut crate::leanh::LeanObject,
    mut v_arg_3623_: *mut crate::leanh::LeanObject,
    mut v___x_3624_: *mut crate::leanh::LeanObject,
    mut v_arg_3625_: *mut crate::leanh::LeanObject,
    mut v___y_3626_: *mut crate::leanh::LeanObject,
    mut v___y_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v_val_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v_a_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3632_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3614_,
                    v_expr_3615_,
                    v___y_3626_,
                    v___y_3627_,
                    v___y_3628_,
                    v___y_3629_,
                    v___y_3630_,
                );
                if crate::leanh::lean_obj_tag(v___x_3632_) == 0 {
                    v_a_3633_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
                    crate::leanh::lean_inc(v_a_3633_);
                    crate::leanh::lean_dec_ref_known(v___x_3632_, 1);
                    v___x_3634_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                        v_val_3616_,
                        v___y_3626_,
                        v___y_3627_,
                        v___y_3628_,
                        v___y_3629_,
                        v___y_3630_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3634_) == 0 {
                        v_a_3635_ = crate::leanh::lean_ctor_get(v___x_3634_, 0);
                        v_isSharedCheck_3659_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3634_)) as u8;
                        if v_isSharedCheck_3659_ == 0 {
                            v___x_3637_ = v___x_3634_;
                            v_isShared_3638_ = v_isSharedCheck_3659_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3635_);
                            crate::leanh::lean_dec(v___x_3634_);
                            v___x_3637_ = crate::leanh::lean_box(0);
                            v_isShared_3638_ = v_isSharedCheck_3659_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3633_);
                        crate::leanh::lean_dec_ref(v_arg_3625_);
                        crate::leanh::lean_dec_ref(v___x_3624_);
                        crate::leanh::lean_dec_ref(v_arg_3623_);
                        crate::leanh::lean_dec_ref(v_arg_3622_);
                        crate::leanh::lean_dec(v___x_3621_);
                        crate::leanh::lean_dec_ref(v___x_3620_);
                        crate::leanh::lean_dec_ref(v___x_3619_);
                        crate::leanh::lean_dec_ref(v___x_3618_);
                        crate::leanh::lean_dec_ref(v___x_3617_);
                        return v___x_3634_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_arg_3625_);
                    crate::leanh::lean_dec_ref(v___x_3624_);
                    crate::leanh::lean_dec_ref(v_arg_3623_);
                    crate::leanh::lean_dec_ref(v_arg_3622_);
                    crate::leanh::lean_dec(v___x_3621_);
                    crate::leanh::lean_dec_ref(v___x_3620_);
                    crate::leanh::lean_dec_ref(v___x_3619_);
                    crate::leanh::lean_dec_ref(v___x_3618_);
                    crate::leanh::lean_dec_ref(v___x_3617_);
                    crate::leanh::lean_dec_ref(v_val_3616_);
                    v_a_3660_ = crate::leanh::lean_ctor_get(v___x_3632_, 0);
                    v_isSharedCheck_3667_ = (!crate::leanh::lean_is_exclusive(v___x_3632_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v___x_3662_ = v___x_3632_;
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3660_);
                        crate::leanh::lean_dec(v___x_3632_);
                        v___x_3662_ = crate::leanh::lean_box(0);
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3635_) == 1 {
                    v_val_3639_ = crate::leanh::lean_ctor_get(v_a_3635_, 0);
                    v_isSharedCheck_3654_ = (!crate::leanh::lean_is_exclusive(v_a_3635_)) as u8;
                    if v_isSharedCheck_3654_ == 0 {
                        v___x_3641_ = v_a_3635_;
                        v_isShared_3642_ = v_isSharedCheck_3654_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3639_);
                        crate::leanh::lean_dec(v_a_3635_);
                        v___x_3641_ = crate::leanh::lean_box(0);
                        v_isShared_3642_ = v_isSharedCheck_3654_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3635_);
                    crate::leanh::lean_dec(v_a_3633_);
                    crate::leanh::lean_dec_ref(v_arg_3625_);
                    crate::leanh::lean_dec_ref(v___x_3624_);
                    crate::leanh::lean_dec_ref(v_arg_3623_);
                    crate::leanh::lean_dec_ref(v_arg_3622_);
                    crate::leanh::lean_dec(v___x_3621_);
                    crate::leanh::lean_dec_ref(v___x_3620_);
                    crate::leanh::lean_dec_ref(v___x_3619_);
                    crate::leanh::lean_dec_ref(v___x_3618_);
                    crate::leanh::lean_dec_ref(v___x_3617_);
                    v___x_3655_ = crate::leanh::lean_box(0);
                    if v_isShared_3638_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3637_, 0, v___x_3655_);
                        v___x_3657_ = v___x_3637_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3658_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
                        v___x_3657_ = v_reuseFailAlloc_3658_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3643_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0;
                v___x_3644_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___closed__0;
                v___x_3645_ = l_Lean_Name_mkStr6(
                    v___x_3617_,
                    v___x_3618_,
                    v___x_3619_,
                    v___x_3643_,
                    v___x_3620_,
                    v___x_3644_,
                );
                v___x_3646_ = l_Lean_mkConst(v___x_3645_, v___x_3621_);
                v___x_3647_ = l_Lean_mkApp6(
                    v___x_3646_,
                    v_arg_3622_,
                    v_arg_3623_,
                    v___x_3624_,
                    v_arg_3625_,
                    v_a_3633_,
                    v_val_3639_,
                );
                if v_isShared_3642_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3641_, 0, v___x_3647_);
                    v___x_3649_ = v___x_3641_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3647_);
                    v___x_3649_ = v_reuseFailAlloc_3653_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3637_, 0, v___x_3649_);
                    v___x_3651_ = v___x_3637_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
                    v___x_3651_ = v_reuseFailAlloc_3652_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3651_;
            }
            5 => {
                return v___x_3657_;
            }
            6 => {
                if v_isShared_3663_ == 0 {
                    v___x_3665_ = v___x_3662_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
                    v___x_3665_ = v_reuseFailAlloc_3666_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_width_3668_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_expr_3669_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_val_3670_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3671_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_3672_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3673_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3674_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3675_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_arg_3676_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_arg_3677_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_3678_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_arg_3679_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3680_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3681_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3682_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3683_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3684_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3685_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(v_width_3668_, v_expr_3669_, v_val_3670_, v___x_3671_, v___x_3672_, v___x_3673_, v___x_3674_, v___x_3675_, v_arg_3676_, v_arg_3677_, v___x_3678_, v_arg_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
    crate::leanh::lean_dec(v___y_3684_);
    crate::leanh::lean_dec_ref(v___y_3683_);
    crate::leanh::lean_dec(v___y_3682_);
    crate::leanh::lean_dec_ref(v___y_3681_);
    crate::leanh::lean_dec(v___y_3680_);
    return v_res_3686_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2(
    mut v_n_3687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3688_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3688_, 0, v_n_3687_);
    return v___x_3688_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ = crate::leanh::lean_box(0);
    v___x_3804_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1;
    v___x_3805_ = l_Lean_mkConst(v___x_3804_, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = crate::leanh::lean_box(0);
    v___x_3815_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5;
    v___x_3816_ = l_Lean_mkConst(v___x_3815_, v___x_3814_);
    return v___x_3816_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3824_ = crate::leanh::lean_box(0);
    v___x_3825_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8;
    v___x_3826_ = l_Lean_mkConst(v___x_3825_, v___x_3824_);
    return v___x_3826_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3834_ = crate::leanh::lean_box(0);
    v___x_3835_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11;
    v___x_3836_ = l_Lean_mkConst(v___x_3835_, v___x_3834_);
    return v___x_3836_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = crate::leanh::lean_box(0);
    v___x_3845_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14;
    v___x_3846_ = l_Lean_mkConst(v___x_3845_, v___x_3844_);
    return v___x_3846_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = crate::leanh::lean_box(0);
    v___x_3855_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17;
    v___x_3856_ = l_Lean_mkConst(v___x_3855_, v___x_3854_);
    return v___x_3856_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = crate::leanh::lean_box(0);
    v___x_3865_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20;
    v___x_3866_ = l_Lean_mkConst(v___x_3865_, v___x_3864_);
    return v___x_3866_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = crate::leanh::lean_box(0);
    v___x_3875_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23;
    v___x_3876_ = l_Lean_mkConst(v___x_3875_, v___x_3874_);
    return v___x_3876_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(
    mut v_lhsExpr_3877_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_3878_: *mut crate::leanh::LeanObject,
    mut v_op_3879_: u8,
    mut v_congrThm_3880_: *mut crate::leanh::LeanObject,
    mut v_origExpr_3881_: *mut crate::leanh::LeanObject,
    mut v_a_3882_: *mut crate::leanh::LeanObject,
    mut v_a_3883_: *mut crate::leanh::LeanObject,
    mut v_a_3884_: *mut crate::leanh::LeanObject,
    mut v_a_3885_: *mut crate::leanh::LeanObject,
    mut v_a_3886_: *mut crate::leanh::LeanObject,
    mut v_a_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v_val_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v_val_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3903_: u8 = 0;
    let mut v_width_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3939_: u8 = 0;
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_lhsExpr_3877_);
                v___x_3889_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_lhsExpr_3877_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
                if crate::leanh::lean_obj_tag(v___x_3889_) == 0 {
                    v_a_3890_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
                    v_isSharedCheck_3949_ = (!crate::leanh::lean_is_exclusive(v___x_3889_)) as u8;
                    if v_isSharedCheck_3949_ == 0 {
                        v___x_3892_ = v___x_3889_;
                        v_isShared_3893_ = v_isSharedCheck_3949_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3890_);
                        crate::leanh::lean_dec(v___x_3889_);
                        v___x_3892_ = crate::leanh::lean_box(0);
                        v_isShared_3893_ = v_isSharedCheck_3949_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_3881_);
                    crate::leanh::lean_dec(v_congrThm_3880_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_3878_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_3877_);
                    return v___x_3889_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3890_) == 1 {
                    crate::leanh::lean_del_object(v___x_3892_);
                    v_val_3894_ = crate::leanh::lean_ctor_get(v_a_3890_, 0);
                    crate::leanh::lean_inc(v_val_3894_);
                    crate::leanh::lean_dec_ref_known(v_a_3890_, 1);
                    crate::leanh::lean_inc_ref(v_rhsExpr_3878_);
                    v___x_3895_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_rhsExpr_3878_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
                    if crate::leanh::lean_obj_tag(v___x_3895_) == 0 {
                        v_a_3896_ = crate::leanh::lean_ctor_get(v___x_3895_, 0);
                        v_isSharedCheck_3944_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3895_)) as u8;
                        if v_isSharedCheck_3944_ == 0 {
                            v___x_3898_ = v___x_3895_;
                            v_isShared_3899_ = v_isSharedCheck_3944_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3896_);
                            crate::leanh::lean_dec(v___x_3895_);
                            v___x_3898_ = crate::leanh::lean_box(0);
                            v_isShared_3899_ = v_isSharedCheck_3944_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3894_);
                        crate::leanh::lean_dec_ref(v_origExpr_3881_);
                        crate::leanh::lean_dec(v_congrThm_3880_);
                        crate::leanh::lean_dec_ref(v_rhsExpr_3878_);
                        crate::leanh::lean_dec_ref(v_lhsExpr_3877_);
                        return v___x_3895_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3890_);
                    crate::leanh::lean_dec_ref(v_origExpr_3881_);
                    crate::leanh::lean_dec(v_congrThm_3880_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_3878_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_3877_);
                    v___x_3945_ = crate::leanh::lean_box(0);
                    if v_isShared_3893_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3892_, 0, v___x_3945_);
                        v___x_3947_ = v___x_3892_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
                        v___x_3947_ = v_reuseFailAlloc_3948_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3896_) == 1 {
                    v_val_3900_ = crate::leanh::lean_ctor_get(v_a_3896_, 0);
                    v_isSharedCheck_3939_ = (!crate::leanh::lean_is_exclusive(v_a_3896_)) as u8;
                    if v_isSharedCheck_3939_ == 0 {
                        v___x_3902_ = v_a_3896_;
                        v_isShared_3903_ = v_isSharedCheck_3939_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3900_);
                        crate::leanh::lean_dec(v_a_3896_);
                        v___x_3902_ = crate::leanh::lean_box(0);
                        v_isShared_3903_ = v_isSharedCheck_3939_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3896_);
                    crate::leanh::lean_dec(v_val_3894_);
                    crate::leanh::lean_dec_ref(v_origExpr_3881_);
                    crate::leanh::lean_dec(v_congrThm_3880_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_3878_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_3877_);
                    v___x_3940_ = crate::leanh::lean_box(0);
                    if v_isShared_3899_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3940_);
                        v___x_3942_ = v___x_3898_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3943_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
                        v___x_3942_ = v_reuseFailAlloc_3943_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_width_3904_ = crate::leanh::lean_ctor_get(v_val_3900_, 0);
                v_bvExpr_3905_ = crate::leanh::lean_ctor_get(v_val_3900_, 1);
                v_expr_3906_ = crate::leanh::lean_ctor_get(v_val_3900_, 4);
                v_width_3907_ = crate::leanh::lean_ctor_get(v_val_3894_, 0);
                crate::leanh::lean_inc(v_width_3907_);
                v_bvExpr_3908_ = crate::leanh::lean_ctor_get(v_val_3894_, 1);
                v_expr_3909_ = crate::leanh::lean_ctor_get(v_val_3894_, 4);
                v___x_3910_ = lean_nat_dec_eq(v_width_3904_, v_width_3907_);
                if v___x_3910_ == 0 {
                    crate::leanh::lean_dec(v_width_3907_);
                    crate::leanh::lean_del_object(v___x_3902_);
                    crate::leanh::lean_dec(v_val_3900_);
                    crate::leanh::lean_dec(v_val_3894_);
                    crate::leanh::lean_dec_ref(v_origExpr_3881_);
                    crate::leanh::lean_dec(v_congrThm_3880_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_3878_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_3877_);
                    v___x_3911_ = crate::leanh::lean_box(0);
                    if v_isShared_3899_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3911_);
                        v___x_3913_ = v___x_3898_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
                        v___x_3913_ = v_reuseFailAlloc_3914_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_bvExpr_3905_);
                    crate::leanh::lean_inc_ref(v_bvExpr_3908_);
                    crate::leanh::lean_inc_n(v_width_3907_, 2);
                    v___x_3915_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(
                        v_width_3907_,
                        v_bvExpr_3908_,
                        v_op_3879_,
                        v_bvExpr_3905_,
                    );
                    v___x_3916_ = crate::leanh::lean_box(0);
                    v___x_3917_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2);
                    v___x_3918_ = l_Lean_mkNatLit(v_width_3907_);
                    match v_op_3879_ {
                        0 => {
                            v___x_3932_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6);
                            v___y_3920_ = v___x_3932_;
                            state = 5;
                            continue;
                        }
                        1 => {
                            v___x_3933_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9);
                            v___y_3920_ = v___x_3933_;
                            state = 5;
                            continue;
                        }
                        2 => {
                            v___x_3934_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12);
                            v___y_3920_ = v___x_3934_;
                            state = 5;
                            continue;
                        }
                        3 => {
                            v___x_3935_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15);
                            v___y_3920_ = v___x_3935_;
                            state = 5;
                            continue;
                        }
                        4 => {
                            v___x_3936_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18);
                            v___y_3920_ = v___x_3936_;
                            state = 5;
                            continue;
                        }
                        5 => {
                            v___x_3937_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21);
                            v___y_3920_ = v___x_3937_;
                            state = 5;
                            continue;
                        }
                        _ => {
                            v___x_3938_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24);
                            v___y_3920_ = v___x_3938_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_3913_;
            }
            5 => {
                crate::leanh::lean_inc_ref(v_expr_3906_);
                crate::leanh::lean_inc_ref(v___y_3920_);
                crate::leanh::lean_inc_ref(v_expr_3909_);
                crate::leanh::lean_inc_ref(v___x_3918_);
                v___x_3921_ = l_Lean_mkApp4(
                    v___x_3917_,
                    v___x_3918_,
                    v_expr_3909_,
                    v___y_3920_,
                    v_expr_3906_,
                );
                v___x_3922_ = l_Lean_mkConst(v_congrThm_3880_, v___x_3916_);
                v___x_3923_ = l_Lean_Expr_app___override(v___x_3922_, v___x_3918_);
                v___x_3924_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed as *mut core::ffi::c_void, 11, 5);
                crate::leanh::lean_closure_set(v___x_3924_, 0, v_val_3894_);
                crate::leanh::lean_closure_set(v___x_3924_, 1, v_val_3900_);
                crate::leanh::lean_closure_set(v___x_3924_, 2, v_lhsExpr_3877_);
                crate::leanh::lean_closure_set(v___x_3924_, 3, v_rhsExpr_3878_);
                crate::leanh::lean_closure_set(v___x_3924_, 4, v___x_3923_);
                v___x_3925_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3925_, 0, v_width_3907_);
                crate::leanh::lean_ctor_set(v___x_3925_, 1, v___x_3915_);
                crate::leanh::lean_ctor_set(v___x_3925_, 2, v_origExpr_3881_);
                crate::leanh::lean_ctor_set(v___x_3925_, 3, v___x_3924_);
                crate::leanh::lean_ctor_set(v___x_3925_, 4, v___x_3921_);
                if v_isShared_3903_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3902_, 0, v___x_3925_);
                    v___x_3927_ = v___x_3902_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3925_);
                    v___x_3927_ = v_reuseFailAlloc_3931_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3927_);
                    v___x_3929_ = v___x_3898_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
                    v___x_3929_ = v_reuseFailAlloc_3930_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3929_;
            }
            8 => {
                return v___x_3942_;
            }
            9 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(
    mut v_distanceExpr_4008_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_4009_: *mut crate::leanh::LeanObject,
    mut v_shiftOp_4010_: *mut crate::leanh::LeanObject,
    mut v_shiftOpName_4011_: *mut crate::leanh::LeanObject,
    mut v_congrThm_4012_: *mut crate::leanh::LeanObject,
    mut v_origExpr_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
    mut v_a_4015_: *mut crate::leanh::LeanObject,
    mut v_a_4016_: *mut crate::leanh::LeanObject,
    mut v_a_4017_: *mut crate::leanh::LeanObject,
    mut v_a_4018_: *mut crate::leanh::LeanObject,
    mut v_a_4019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v_val_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v_val_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v_width_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_innerExpr_4009_);
                v___x_4021_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4009_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
                if crate::leanh::lean_obj_tag(v___x_4021_) == 0 {
                    v_a_4022_ = crate::leanh::lean_ctor_get(v___x_4021_, 0);
                    v_isSharedCheck_4068_ = (!crate::leanh::lean_is_exclusive(v___x_4021_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v___x_4024_ = v___x_4021_;
                        v_isShared_4025_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4022_);
                        crate::leanh::lean_dec(v___x_4021_);
                        v___x_4024_ = crate::leanh::lean_box(0);
                        v_isShared_4025_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4013_);
                    crate::leanh::lean_dec(v_congrThm_4012_);
                    crate::leanh::lean_dec(v_shiftOpName_4011_);
                    crate::leanh::lean_dec_ref(v_shiftOp_4010_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4009_);
                    crate::leanh::lean_dec_ref(v_distanceExpr_4008_);
                    return v___x_4021_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4022_) == 1 {
                    crate::leanh::lean_del_object(v___x_4024_);
                    v_val_4026_ = crate::leanh::lean_ctor_get(v_a_4022_, 0);
                    crate::leanh::lean_inc(v_val_4026_);
                    crate::leanh::lean_dec_ref_known(v_a_4022_, 1);
                    crate::leanh::lean_inc_ref(v_distanceExpr_4008_);
                    v___x_4027_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_distanceExpr_4008_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
                    if crate::leanh::lean_obj_tag(v___x_4027_) == 0 {
                        v_a_4028_ = crate::leanh::lean_ctor_get(v___x_4027_, 0);
                        v_isSharedCheck_4063_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4027_)) as u8;
                        if v_isSharedCheck_4063_ == 0 {
                            v___x_4030_ = v___x_4027_;
                            v_isShared_4031_ = v_isSharedCheck_4063_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4028_);
                            crate::leanh::lean_dec(v___x_4027_);
                            v___x_4030_ = crate::leanh::lean_box(0);
                            v_isShared_4031_ = v_isSharedCheck_4063_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4026_);
                        crate::leanh::lean_dec_ref(v_origExpr_4013_);
                        crate::leanh::lean_dec(v_congrThm_4012_);
                        crate::leanh::lean_dec(v_shiftOpName_4011_);
                        crate::leanh::lean_dec_ref(v_shiftOp_4010_);
                        crate::leanh::lean_dec_ref(v_innerExpr_4009_);
                        crate::leanh::lean_dec_ref(v_distanceExpr_4008_);
                        return v___x_4027_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4022_);
                    crate::leanh::lean_dec_ref(v_origExpr_4013_);
                    crate::leanh::lean_dec(v_congrThm_4012_);
                    crate::leanh::lean_dec(v_shiftOpName_4011_);
                    crate::leanh::lean_dec_ref(v_shiftOp_4010_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4009_);
                    crate::leanh::lean_dec_ref(v_distanceExpr_4008_);
                    v___x_4064_ = crate::leanh::lean_box(0);
                    if v_isShared_4025_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4024_, 0, v___x_4064_);
                        v___x_4066_ = v___x_4024_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4067_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
                        v___x_4066_ = v_reuseFailAlloc_4067_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4028_) == 1 {
                    v_val_4032_ = crate::leanh::lean_ctor_get(v_a_4028_, 0);
                    v_isSharedCheck_4058_ = (!crate::leanh::lean_is_exclusive(v_a_4028_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4034_ = v_a_4028_;
                        v_isShared_4035_ = v_isSharedCheck_4058_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4032_);
                        crate::leanh::lean_dec(v_a_4028_);
                        v___x_4034_ = crate::leanh::lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4058_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4028_);
                    crate::leanh::lean_dec(v_val_4026_);
                    crate::leanh::lean_dec_ref(v_origExpr_4013_);
                    crate::leanh::lean_dec(v_congrThm_4012_);
                    crate::leanh::lean_dec(v_shiftOpName_4011_);
                    crate::leanh::lean_dec_ref(v_shiftOp_4010_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4009_);
                    crate::leanh::lean_dec_ref(v_distanceExpr_4008_);
                    v___x_4059_ = crate::leanh::lean_box(0);
                    if v_isShared_4031_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4030_, 0, v___x_4059_);
                        v___x_4061_ = v___x_4030_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
                        v___x_4061_ = v_reuseFailAlloc_4062_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_width_4036_ = crate::leanh::lean_ctor_get(v_val_4026_, 0);
                crate::leanh::lean_inc_n(v_width_4036_, 3);
                v_bvExpr_4037_ = crate::leanh::lean_ctor_get(v_val_4026_, 1);
                v_expr_4038_ = crate::leanh::lean_ctor_get(v_val_4026_, 4);
                v_width_4039_ = crate::leanh::lean_ctor_get(v_val_4032_, 0);
                v_bvExpr_4040_ = crate::leanh::lean_ctor_get(v_val_4032_, 1);
                v_expr_4041_ = crate::leanh::lean_ctor_get(v_val_4032_, 4);
                crate::leanh::lean_inc_ref(v_bvExpr_4040_);
                crate::leanh::lean_inc_ref(v_bvExpr_4037_);
                crate::leanh::lean_inc_n(v_width_4039_, 2);
                v___x_4042_ = crate::leanh::lean_apply_4(
                    v_shiftOp_4010_,
                    v_width_4036_,
                    v_width_4039_,
                    v_bvExpr_4037_,
                    v_bvExpr_4040_,
                );
                v___x_4043_ = crate::leanh::lean_box(0);
                v___x_4044_ = l_Lean_mkConst(v_shiftOpName_4011_, v___x_4043_);
                v___x_4045_ = l_Lean_mkNatLit(v_width_4036_);
                v___x_4046_ = l_Lean_mkNatLit(v_width_4039_);
                crate::leanh::lean_inc_ref(v_expr_4041_);
                crate::leanh::lean_inc_ref(v_expr_4038_);
                crate::leanh::lean_inc_ref(v___x_4046_);
                crate::leanh::lean_inc_ref(v___x_4045_);
                v___x_4047_ = l_Lean_mkApp4(
                    v___x_4044_,
                    v___x_4045_,
                    v___x_4046_,
                    v_expr_4038_,
                    v_expr_4041_,
                );
                v___x_4048_ = l_Lean_mkConst(v_congrThm_4012_, v___x_4043_);
                v___x_4049_ = l_Lean_mkAppB(v___x_4048_, v___x_4045_, v___x_4046_);
                v___x_4050_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed as *mut core::ffi::c_void, 11, 5);
                crate::leanh::lean_closure_set(v___x_4050_, 0, v_val_4026_);
                crate::leanh::lean_closure_set(v___x_4050_, 1, v_val_4032_);
                crate::leanh::lean_closure_set(v___x_4050_, 2, v_innerExpr_4009_);
                crate::leanh::lean_closure_set(v___x_4050_, 3, v_distanceExpr_4008_);
                crate::leanh::lean_closure_set(v___x_4050_, 4, v___x_4049_);
                v___x_4051_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4051_, 0, v_width_4036_);
                crate::leanh::lean_ctor_set(v___x_4051_, 1, v___x_4042_);
                crate::leanh::lean_ctor_set(v___x_4051_, 2, v_origExpr_4013_);
                crate::leanh::lean_ctor_set(v___x_4051_, 3, v___x_4050_);
                crate::leanh::lean_ctor_set(v___x_4051_, 4, v___x_4047_);
                if v_isShared_4035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4034_, 0, v___x_4051_);
                    v___x_4053_ = v___x_4034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4051_);
                    v___x_4053_ = v_reuseFailAlloc_4057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4031_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4030_, 0, v___x_4053_);
                    v___x_4055_ = v___x_4030_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
                    v___x_4055_ = v_reuseFailAlloc_4056_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4055_;
            }
            6 => {
                return v___x_4061_;
            }
            7 => {
                return v___x_4066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4070_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62;
    v___x_4071_ = l_Lean_stringToMessageData(v___x_4070_);
    return v___x_4071_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = crate::leanh::lean_box(0);
    v___x_4096_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70;
    v___x_4097_ = l_Lean_mkConst(v___x_4096_, v___x_4095_);
    return v___x_4097_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4121_ = crate::leanh::lean_box(0);
    v___x_4122_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78;
    v___x_4123_ = l_Lean_mkConst(v___x_4122_, v___x_4121_);
    return v___x_4123_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(
    mut v_lhsExpr_4146_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_4147_: *mut crate::leanh::LeanObject,
    mut v_pred_4148_: u8,
    mut v_origExpr_4149_: *mut crate::leanh::LeanObject,
    mut v_a_4150_: *mut crate::leanh::LeanObject,
    mut v_a_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
    mut v_a_4154_: *mut crate::leanh::LeanObject,
    mut v_a_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4161_: u8 = 0;
    let mut v_val_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4167_: u8 = 0;
    let mut v_val_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4174_: u8 = 0;
    let mut v_a_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4187_: u8 = 0;
    let mut v_a_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4191_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_lhsExpr_4146_);
                v___x_4157_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
                    v_lhsExpr_4146_,
                    v_a_4150_,
                    v_a_4151_,
                    v_a_4152_,
                    v_a_4153_,
                    v_a_4154_,
                    v_a_4155_,
                );
                if crate::leanh::lean_obj_tag(v___x_4157_) == 0 {
                    v_a_4158_ = crate::leanh::lean_ctor_get(v___x_4157_, 0);
                    v_isSharedCheck_4187_ = (!crate::leanh::lean_is_exclusive(v___x_4157_)) as u8;
                    if v_isSharedCheck_4187_ == 0 {
                        v___x_4160_ = v___x_4157_;
                        v_isShared_4161_ = v_isSharedCheck_4187_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4158_);
                        crate::leanh::lean_dec(v___x_4157_);
                        v___x_4160_ = crate::leanh::lean_box(0);
                        v_isShared_4161_ = v_isSharedCheck_4187_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4149_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_4147_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_4146_);
                    v_a_4188_ = crate::leanh::lean_ctor_get(v___x_4157_, 0);
                    v_isSharedCheck_4195_ = (!crate::leanh::lean_is_exclusive(v___x_4157_)) as u8;
                    if v_isSharedCheck_4195_ == 0 {
                        v___x_4190_ = v___x_4157_;
                        v_isShared_4191_ = v_isSharedCheck_4195_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4188_);
                        crate::leanh::lean_dec(v___x_4157_);
                        v___x_4190_ = crate::leanh::lean_box(0);
                        v_isShared_4191_ = v_isSharedCheck_4195_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4158_) == 1 {
                    crate::leanh::lean_del_object(v___x_4160_);
                    v_val_4162_ = crate::leanh::lean_ctor_get(v_a_4158_, 0);
                    crate::leanh::lean_inc(v_val_4162_);
                    crate::leanh::lean_dec_ref_known(v_a_4158_, 1);
                    crate::leanh::lean_inc_ref(v_rhsExpr_4147_);
                    v___x_4163_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
                        v_rhsExpr_4147_,
                        v_a_4150_,
                        v_a_4151_,
                        v_a_4152_,
                        v_a_4153_,
                        v_a_4154_,
                        v_a_4155_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4163_) == 0 {
                        v_a_4164_ = crate::leanh::lean_ctor_get(v___x_4163_, 0);
                        v_isSharedCheck_4174_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4163_)) as u8;
                        if v_isSharedCheck_4174_ == 0 {
                            v___x_4166_ = v___x_4163_;
                            v_isShared_4167_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4164_);
                            crate::leanh::lean_dec(v___x_4163_);
                            v___x_4166_ = crate::leanh::lean_box(0);
                            v_isShared_4167_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4162_);
                        crate::leanh::lean_dec_ref(v_origExpr_4149_);
                        crate::leanh::lean_dec_ref(v_rhsExpr_4147_);
                        crate::leanh::lean_dec_ref(v_lhsExpr_4146_);
                        v_a_4175_ = crate::leanh::lean_ctor_get(v___x_4163_, 0);
                        v_isSharedCheck_4182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4163_)) as u8;
                        if v_isSharedCheck_4182_ == 0 {
                            v___x_4177_ = v___x_4163_;
                            v_isShared_4178_ = v_isSharedCheck_4182_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4175_);
                            crate::leanh::lean_dec(v___x_4163_);
                            v___x_4177_ = crate::leanh::lean_box(0);
                            v_isShared_4178_ = v_isSharedCheck_4182_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4158_);
                    crate::leanh::lean_dec_ref(v_origExpr_4149_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_4147_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_4146_);
                    v___x_4183_ = crate::leanh::lean_box(0);
                    if v_isShared_4161_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4160_, 0, v___x_4183_);
                        v___x_4185_ = v___x_4160_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
                        v___x_4185_ = v_reuseFailAlloc_4186_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4164_) == 1 {
                    crate::leanh::lean_del_object(v___x_4166_);
                    v_val_4168_ = crate::leanh::lean_ctor_get(v_a_4164_, 0);
                    crate::leanh::lean_inc(v_val_4168_);
                    crate::leanh::lean_dec_ref_known(v_a_4164_, 1);
                    v___x_4169_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(
                        v_val_4162_,
                        v_val_4168_,
                        v_lhsExpr_4146_,
                        v_rhsExpr_4147_,
                        v_pred_4148_,
                        v_origExpr_4149_,
                    );
                    return v___x_4169_;
                } else {
                    crate::leanh::lean_dec(v_a_4164_);
                    crate::leanh::lean_dec(v_val_4162_);
                    crate::leanh::lean_dec_ref(v_origExpr_4149_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_4147_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_4146_);
                    v___x_4170_ = crate::leanh::lean_box(0);
                    if v_isShared_4167_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4166_, 0, v___x_4170_);
                        v___x_4172_ = v___x_4166_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
                        v___x_4172_ = v_reuseFailAlloc_4173_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4172_;
            }
            4 => {
                if v_isShared_4178_ == 0 {
                    v___x_4180_ = v___x_4177_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
                    v___x_4180_ = v_reuseFailAlloc_4181_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4180_;
            }
            6 => {
                return v___x_4185_;
            }
            7 => {
                if v_isShared_4191_ == 0 {
                    v___x_4193_ = v___x_4190_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4194_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
                    v___x_4193_ = v_reuseFailAlloc_4194_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4193_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(
    mut v_origExpr_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: u8 = 0;
    let mut v_arg_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: u8 = 0;
    let mut v_arg_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: u8 = 0;
    let mut v___x_4230_: u8 = 0;
    let mut v_arg_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: u8 = 0;
    let mut v___x_4240_: u8 = 0;
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: u8 = 0;
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v_val_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v_val_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4263_: u8 = 0;
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v_a_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut v_a_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut v_a_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut v_isSharedCheck_4306_: u8 = 0;
    let mut v_a_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4310_: u8 = 0;
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_origExpr_4196_);
                v___x_4207_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_4196_, v_a_4200_);
                if crate::leanh::lean_obj_tag(v___x_4207_) == 0 {
                    v_a_4208_ = crate::leanh::lean_ctor_get(v___x_4207_, 0);
                    v_isSharedCheck_4306_ = (!crate::leanh::lean_is_exclusive(v___x_4207_)) as u8;
                    if v_isSharedCheck_4306_ == 0 {
                        v___x_4210_ = v___x_4207_;
                        v_isShared_4211_ = v_isSharedCheck_4306_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4208_);
                        crate::leanh::lean_dec(v___x_4207_);
                        v___x_4210_ = crate::leanh::lean_box(0);
                        v_isShared_4211_ = v_isSharedCheck_4306_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4196_);
                    v_a_4307_ = crate::leanh::lean_ctor_get(v___x_4207_, 0);
                    v_isSharedCheck_4314_ = (!crate::leanh::lean_is_exclusive(v___x_4207_)) as u8;
                    if v_isSharedCheck_4314_ == 0 {
                        v___x_4309_ = v___x_4207_;
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4307_);
                        crate::leanh::lean_dec(v___x_4207_);
                        v___x_4309_ = crate::leanh::lean_box(0);
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4205_ = crate::leanh::lean_box(0);
                v___x_4206_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4206_, 0, v___x_4205_);
                return v___x_4206_;
            }
            2 => {
                v___x_4217_ = l_Lean_Expr_cleanupAnnotations(v_a_4208_);
                v___x_4218_ = l_Lean_Expr_isApp(v___x_4217_);
                if v___x_4218_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4217_);
                    crate::leanh::lean_dec_ref(v_origExpr_4196_);
                    state = 3;
                    continue;
                } else {
                    v_arg_4219_ = crate::leanh::lean_ctor_get(v___x_4217_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4219_);
                    v___x_4220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4217_);
                    v___x_4221_ = l_Lean_Expr_isApp(v___x_4220_);
                    if v___x_4221_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4220_);
                        crate::leanh::lean_dec_ref(v_arg_4219_);
                        crate::leanh::lean_dec_ref(v_origExpr_4196_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_4222_ = crate::leanh::lean_ctor_get(v___x_4220_, 1);
                        crate::leanh::lean_inc_ref(v_arg_4222_);
                        v___x_4223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4220_);
                        v___x_4224_ = l_Lean_Expr_isApp(v___x_4223_);
                        if v___x_4224_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4223_);
                            crate::leanh::lean_dec_ref(v_arg_4222_);
                            crate::leanh::lean_dec_ref(v_arg_4219_);
                            crate::leanh::lean_dec_ref(v_origExpr_4196_);
                            state = 3;
                            continue;
                        } else {
                            v___x_4225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4223_);
                            v___x_4226_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2;
                            v___x_4227_ = l_Lean_Expr_isConstOf(v___x_4225_, v___x_4226_);
                            if v___x_4227_ == 0 {
                                v___x_4228_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4;
                                v___x_4229_ = l_Lean_Expr_isConstOf(v___x_4225_, v___x_4228_);
                                if v___x_4229_ == 0 {
                                    v___x_4230_ = l_Lean_Expr_isApp(v___x_4225_);
                                    if v___x_4230_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_4225_);
                                        crate::leanh::lean_dec_ref(v_arg_4222_);
                                        crate::leanh::lean_dec_ref(v_arg_4219_);
                                        crate::leanh::lean_dec_ref(v_origExpr_4196_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v_arg_4231_ = crate::leanh::lean_ctor_get(v___x_4225_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_4231_);
                                        v___x_4232_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4225_);
                                        v___x_4233_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7;
                                        v___x_4234_ =
                                            l_Lean_Expr_isConstOf(v___x_4232_, v___x_4233_);
                                        crate::leanh::lean_dec_ref(v___x_4232_);
                                        if v___x_4234_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_4231_);
                                            crate::leanh::lean_dec_ref(v_arg_4222_);
                                            crate::leanh::lean_dec_ref(v_arg_4219_);
                                            crate::leanh::lean_dec_ref(v_origExpr_4196_);
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_del_object(v___x_4210_);
                                            v___x_4235_ =
                                                l_Lean_Expr_cleanupAnnotations(v_arg_4231_);
                                            v___x_4236_ = l_Lean_Expr_isApp(v___x_4235_);
                                            if v___x_4236_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_4235_);
                                                crate::leanh::lean_dec_ref(v_arg_4222_);
                                                crate::leanh::lean_dec_ref(v_arg_4219_);
                                                crate::leanh::lean_dec_ref(v_origExpr_4196_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_4237_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_4235_);
                                                v___x_4238_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                                                v___x_4239_ =
                                                    l_Lean_Expr_isConstOf(v___x_4237_, v___x_4238_);
                                                crate::leanh::lean_dec_ref(v___x_4237_);
                                                if v___x_4239_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_arg_4222_);
                                                    crate::leanh::lean_dec_ref(v_arg_4219_);
                                                    crate::leanh::lean_dec_ref(v_origExpr_4196_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_4240_ = 0;
                                                    v___x_4241_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_arg_4222_, v_arg_4219_, v___x_4240_, v_origExpr_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
                                                    return v___x_4241_;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4225_);
                                    crate::leanh::lean_del_object(v___x_4210_);
                                    v___x_4242_ = 1;
                                    v___x_4243_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_arg_4222_, v_arg_4219_, v___x_4242_, v_origExpr_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
                                    return v___x_4243_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4225_);
                                crate::leanh::lean_del_object(v___x_4210_);
                                crate::leanh::lean_inc_ref(v_arg_4222_);
                                v___x_4244_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
                                    v_arg_4222_,
                                    v_a_4197_,
                                    v_a_4198_,
                                    v_a_4199_,
                                    v_a_4200_,
                                    v_a_4201_,
                                    v_a_4202_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4244_) == 0 {
                                    v_a_4245_ = crate::leanh::lean_ctor_get(v___x_4244_, 0);
                                    v_isSharedCheck_4297_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4244_)) as u8;
                                    if v_isSharedCheck_4297_ == 0 {
                                        v___x_4247_ = v___x_4244_;
                                        v_isShared_4248_ = v_isSharedCheck_4297_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4245_);
                                        crate::leanh::lean_dec(v___x_4244_);
                                        v___x_4247_ = crate::leanh::lean_box(0);
                                        v_isShared_4248_ = v_isSharedCheck_4297_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_4222_);
                                    crate::leanh::lean_dec_ref(v_arg_4219_);
                                    crate::leanh::lean_dec_ref(v_origExpr_4196_);
                                    v_a_4298_ = crate::leanh::lean_ctor_get(v___x_4244_, 0);
                                    v_isSharedCheck_4305_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4244_)) as u8;
                                    if v_isSharedCheck_4305_ == 0 {
                                        v___x_4300_ = v___x_4244_;
                                        v_isShared_4301_ = v_isSharedCheck_4305_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4298_);
                                        crate::leanh::lean_dec(v___x_4244_);
                                        v___x_4300_ = crate::leanh::lean_box(0);
                                        v_isShared_4301_ = v_isSharedCheck_4305_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_4213_ = crate::leanh::lean_box(0);
                if v_isShared_4211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4210_, 0, v___x_4213_);
                    v___x_4215_ = v___x_4210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
                    v___x_4215_ = v_reuseFailAlloc_4216_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4215_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4245_) == 1 {
                    crate::leanh::lean_del_object(v___x_4247_);
                    v_val_4249_ = crate::leanh::lean_ctor_get(v_a_4245_, 0);
                    crate::leanh::lean_inc(v_val_4249_);
                    crate::leanh::lean_dec_ref_known(v_a_4245_, 1);
                    v___x_4250_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_4219_,
                        v_a_4199_,
                        v_a_4200_,
                        v_a_4201_,
                        v_a_4202_,
                    );
                    crate::leanh::lean_dec_ref(v_arg_4219_);
                    if crate::leanh::lean_obj_tag(v___x_4250_) == 0 {
                        v_a_4251_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                        v_isSharedCheck_4284_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4250_)) as u8;
                        if v_isSharedCheck_4284_ == 0 {
                            v___x_4253_ = v___x_4250_;
                            v_isShared_4254_ = v_isSharedCheck_4284_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4251_);
                            crate::leanh::lean_dec(v___x_4250_);
                            v___x_4253_ = crate::leanh::lean_box(0);
                            v_isShared_4254_ = v_isSharedCheck_4284_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4249_);
                        crate::leanh::lean_dec_ref(v_arg_4222_);
                        crate::leanh::lean_dec_ref(v_origExpr_4196_);
                        v_a_4285_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                        v_isSharedCheck_4292_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4250_)) as u8;
                        if v_isSharedCheck_4292_ == 0 {
                            v___x_4287_ = v___x_4250_;
                            v_isShared_4288_ = v_isSharedCheck_4292_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4285_);
                            crate::leanh::lean_dec(v___x_4250_);
                            v___x_4287_ = crate::leanh::lean_box(0);
                            v_isShared_4288_ = v_isSharedCheck_4292_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4245_);
                    crate::leanh::lean_dec_ref(v_arg_4222_);
                    crate::leanh::lean_dec_ref(v_arg_4219_);
                    crate::leanh::lean_dec_ref(v_origExpr_4196_);
                    v___x_4293_ = crate::leanh::lean_box(0);
                    if v_isShared_4248_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4247_, 0, v___x_4293_);
                        v___x_4295_ = v___x_4247_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4296_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
                        v___x_4295_ = v_reuseFailAlloc_4296_;
                        state = 16;
                        continue;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_4251_) == 1 {
                    crate::leanh::lean_del_object(v___x_4253_);
                    v_val_4255_ = crate::leanh::lean_ctor_get(v_a_4251_, 0);
                    v_isSharedCheck_4279_ = (!crate::leanh::lean_is_exclusive(v_a_4251_)) as u8;
                    if v_isSharedCheck_4279_ == 0 {
                        v___x_4257_ = v_a_4251_;
                        v_isShared_4258_ = v_isSharedCheck_4279_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4255_);
                        crate::leanh::lean_dec(v_a_4251_);
                        v___x_4257_ = crate::leanh::lean_box(0);
                        v_isShared_4258_ = v_isSharedCheck_4279_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4251_);
                    crate::leanh::lean_dec(v_val_4249_);
                    crate::leanh::lean_dec_ref(v_arg_4222_);
                    crate::leanh::lean_dec_ref(v_origExpr_4196_);
                    v___x_4280_ = crate::leanh::lean_box(0);
                    if v_isShared_4254_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4253_, 0, v___x_4280_);
                        v___x_4282_ = v___x_4253_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4283_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
                        v___x_4282_ = v_reuseFailAlloc_4283_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4259_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(
                    v_val_4249_,
                    v_arg_4222_,
                    v_val_4255_,
                    v_origExpr_4196_,
                );
                if crate::leanh::lean_obj_tag(v___x_4259_) == 0 {
                    v_a_4260_ = crate::leanh::lean_ctor_get(v___x_4259_, 0);
                    v_isSharedCheck_4270_ = (!crate::leanh::lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4270_ == 0 {
                        v___x_4262_ = v___x_4259_;
                        v_isShared_4263_ = v_isSharedCheck_4270_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4260_);
                        crate::leanh::lean_dec(v___x_4259_);
                        v___x_4262_ = crate::leanh::lean_box(0);
                        v_isShared_4263_ = v_isSharedCheck_4270_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4257_);
                    v_a_4271_ = crate::leanh::lean_ctor_get(v___x_4259_, 0);
                    v_isSharedCheck_4278_ = (!crate::leanh::lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4278_ == 0 {
                        v___x_4273_ = v___x_4259_;
                        v_isShared_4274_ = v_isSharedCheck_4278_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4271_);
                        crate::leanh::lean_dec(v___x_4259_);
                        v___x_4273_ = crate::leanh::lean_box(0);
                        v_isShared_4274_ = v_isSharedCheck_4278_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4257_, 0, v_a_4260_);
                    v___x_4265_ = v___x_4257_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4260_);
                    v___x_4265_ = v_reuseFailAlloc_4269_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4263_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4262_, 0, v___x_4265_);
                    v___x_4267_ = v___x_4262_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
                    v___x_4267_ = v_reuseFailAlloc_4268_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4267_;
            }
            11 => {
                if v_isShared_4274_ == 0 {
                    v___x_4276_ = v___x_4273_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
                    v___x_4276_ = v_reuseFailAlloc_4277_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4276_;
            }
            13 => {
                return v___x_4282_;
            }
            14 => {
                if v_isShared_4288_ == 0 {
                    v___x_4290_ = v___x_4287_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
                    v___x_4290_ = v_reuseFailAlloc_4291_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4290_;
            }
            16 => {
                return v___x_4295_;
            }
            17 => {
                if v_isShared_4301_ == 0 {
                    v___x_4303_ = v___x_4300_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
                    v___x_4303_ = v_reuseFailAlloc_4304_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4303_;
            }
            19 => {
                if v_isShared_4310_ == 0 {
                    v___x_4312_ = v___x_4309_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4313_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
                    v___x_4312_ = v_reuseFailAlloc_4313_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(
    mut v_e_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
    mut v_a_4320_: *mut crate::leanh::LeanObject,
    mut v_a_4321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4328_: u8 = 0;
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4356_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4347_ = lean_st_ref_get(v_a_4316_);
                v_bvPredCache_4348_ = crate::leanh::lean_ctor_get(v___x_4347_, 2);
                crate::leanh::lean_inc_ref(v_bvPredCache_4348_);
                crate::leanh::lean_dec(v___x_4347_);
                v___x_4349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvPredCache_4348_, v_e_4315_);
                crate::leanh::lean_dec_ref(v_bvPredCache_4348_);
                if crate::leanh::lean_obj_tag(v___x_4349_) == 0 {
                    crate::leanh::lean_inc_ref(v_e_4315_);
                    v___x_4350_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_e_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
                    if crate::leanh::lean_obj_tag(v___x_4350_) == 0 {
                        v_a_4351_ = crate::leanh::lean_ctor_get(v___x_4350_, 0);
                        crate::leanh::lean_inc(v_a_4351_);
                        if crate::leanh::lean_obj_tag(v_a_4351_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4350_, 1);
                            crate::leanh::lean_inc_ref(v_e_4315_);
                            v___x_4352_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(
                                v_e_4315_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_,
                            );
                            v___y_4324_ = v___x_4352_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_4351_, 1);
                            v___y_4324_ = v___x_4350_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_4324_ = v___x_4350_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4315_);
                    v_val_4353_ = crate::leanh::lean_ctor_get(v___x_4349_, 0);
                    v_isSharedCheck_4360_ = (!crate::leanh::lean_is_exclusive(v___x_4349_)) as u8;
                    if v_isSharedCheck_4360_ == 0 {
                        v___x_4355_ = v___x_4349_;
                        v_isShared_4356_ = v_isSharedCheck_4360_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4353_);
                        crate::leanh::lean_dec(v___x_4349_);
                        v___x_4355_ = crate::leanh::lean_box(0);
                        v_isShared_4356_ = v_isSharedCheck_4360_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4324_) == 0 {
                    v_a_4325_ = crate::leanh::lean_ctor_get(v___y_4324_, 0);
                    v_isSharedCheck_4346_ = (!crate::leanh::lean_is_exclusive(v___y_4324_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4327_ = v___y_4324_;
                        v_isShared_4328_ = v_isSharedCheck_4346_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4325_);
                        crate::leanh::lean_dec(v___y_4324_);
                        v___x_4327_ = crate::leanh::lean_box(0);
                        v_isShared_4328_ = v_isSharedCheck_4346_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4315_);
                    return v___y_4324_;
                }
            }
            2 => {
                v___x_4329_ = lean_st_ref_take(v_a_4316_);
                v_lemmas_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                v_bvExprCache_4331_ = crate::leanh::lean_ctor_get(v___x_4329_, 1);
                v_bvPredCache_4332_ = crate::leanh::lean_ctor_get(v___x_4329_, 2);
                v_bvLogicalCache_4333_ = crate::leanh::lean_ctor_get(v___x_4329_, 3);
                v_isSharedCheck_4345_ = (!crate::leanh::lean_is_exclusive(v___x_4329_)) as u8;
                if v_isSharedCheck_4345_ == 0 {
                    v___x_4335_ = v___x_4329_;
                    v_isShared_4336_ = v_isSharedCheck_4345_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bvLogicalCache_4333_);
                    crate::leanh::lean_inc(v_bvPredCache_4332_);
                    crate::leanh::lean_inc(v_bvExprCache_4331_);
                    crate::leanh::lean_inc(v_lemmas_4330_);
                    crate::leanh::lean_dec(v___x_4329_);
                    v___x_4335_ = crate::leanh::lean_box(0);
                    v_isShared_4336_ = v_isSharedCheck_4345_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_4325_);
                v___x_4337_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvPredCache_4332_, v_e_4315_, v_a_4325_);
                if v_isShared_4336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4335_, 2, v___x_4337_);
                    v___x_4339_ = v___x_4335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4344_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_lemmas_4330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 1, v_bvExprCache_4331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 2, v___x_4337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 3, v_bvLogicalCache_4333_);
                    v___x_4339_ = v_reuseFailAlloc_4344_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4340_ = lean_st_ref_set(v_a_4316_, v___x_4339_);
                if v_isShared_4328_ == 0 {
                    v___x_4342_ = v___x_4327_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4325_);
                    v___x_4342_ = v_reuseFailAlloc_4343_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4342_;
            }
            6 => {
                if v_isShared_4356_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4355_, 0);
                    v___x_4358_ = v___x_4355_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4359_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_val_4353_);
                    v___x_4358_ = v_reuseFailAlloc_4359_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(
    mut v_origExpr_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
    mut v_a_4365_: *mut crate::leanh::LeanObject,
    mut v_a_4366_: *mut crate::leanh::LeanObject,
    mut v_a_4367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4369_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(v_origExpr_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
    return v___x_4369_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(
    mut v_origExpr_4370_: *mut crate::leanh::LeanObject,
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v_val_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4386_: u8 = 0;
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_a_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_a_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4378_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(
                    v_origExpr_4370_,
                    v_a_4371_,
                    v_a_4372_,
                    v_a_4373_,
                    v_a_4374_,
                    v_a_4375_,
                    v_a_4376_,
                );
                if crate::leanh::lean_obj_tag(v___x_4378_) == 0 {
                    v_a_4379_ = crate::leanh::lean_ctor_get(v___x_4378_, 0);
                    v_isSharedCheck_4412_ = (!crate::leanh::lean_is_exclusive(v___x_4378_)) as u8;
                    if v_isSharedCheck_4412_ == 0 {
                        v___x_4381_ = v___x_4378_;
                        v_isShared_4382_ = v_isSharedCheck_4412_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4379_);
                        crate::leanh::lean_dec(v___x_4378_);
                        v___x_4381_ = crate::leanh::lean_box(0);
                        v_isShared_4382_ = v_isSharedCheck_4412_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4413_ = crate::leanh::lean_ctor_get(v___x_4378_, 0);
                    v_isSharedCheck_4420_ = (!crate::leanh::lean_is_exclusive(v___x_4378_)) as u8;
                    if v_isSharedCheck_4420_ == 0 {
                        v___x_4415_ = v___x_4378_;
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4413_);
                        crate::leanh::lean_dec(v___x_4378_);
                        v___x_4415_ = crate::leanh::lean_box(0);
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4379_) == 1 {
                    crate::leanh::lean_del_object(v___x_4381_);
                    v_val_4383_ = crate::leanh::lean_ctor_get(v_a_4379_, 0);
                    v_isSharedCheck_4407_ = (!crate::leanh::lean_is_exclusive(v_a_4379_)) as u8;
                    if v_isSharedCheck_4407_ == 0 {
                        v___x_4385_ = v_a_4379_;
                        v_isShared_4386_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4383_);
                        crate::leanh::lean_dec(v_a_4379_);
                        v___x_4385_ = crate::leanh::lean_box(0);
                        v_isShared_4386_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4379_);
                    v___x_4408_ = crate::leanh::lean_box(0);
                    if v_isShared_4382_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4381_, 0, v___x_4408_);
                        v___x_4410_ = v___x_4381_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4408_);
                        v___x_4410_ = v_reuseFailAlloc_4411_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4387_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_4383_);
                if crate::leanh::lean_obj_tag(v___x_4387_) == 0 {
                    v_a_4388_ = crate::leanh::lean_ctor_get(v___x_4387_, 0);
                    v_isSharedCheck_4398_ = (!crate::leanh::lean_is_exclusive(v___x_4387_)) as u8;
                    if v_isSharedCheck_4398_ == 0 {
                        v___x_4390_ = v___x_4387_;
                        v_isShared_4391_ = v_isSharedCheck_4398_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4388_);
                        crate::leanh::lean_dec(v___x_4387_);
                        v___x_4390_ = crate::leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4398_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4385_);
                    v_a_4399_ = crate::leanh::lean_ctor_get(v___x_4387_, 0);
                    v_isSharedCheck_4406_ = (!crate::leanh::lean_is_exclusive(v___x_4387_)) as u8;
                    if v_isSharedCheck_4406_ == 0 {
                        v___x_4401_ = v___x_4387_;
                        v_isShared_4402_ = v_isSharedCheck_4406_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4399_);
                        crate::leanh::lean_dec(v___x_4387_);
                        v___x_4401_ = crate::leanh::lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4406_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4386_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4385_, 0, v_a_4388_);
                    v___x_4393_ = v___x_4385_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4388_);
                    v___x_4393_ = v_reuseFailAlloc_4397_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4390_, 0, v___x_4393_);
                    v___x_4395_ = v___x_4390_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4395_;
            }
            6 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4404_;
            }
            8 => {
                return v___x_4410_;
            }
            9 => {
                if v_isShared_4416_ == 0 {
                    v___x_4418_ = v___x_4415_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
                    v___x_4418_ = v_reuseFailAlloc_4419_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(
    mut v_lhsExpr_4433_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_4434_: *mut crate::leanh::LeanObject,
    mut v_gate_4435_: u8,
    mut v_origExpr_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
    mut v_a_4439_: *mut crate::leanh::LeanObject,
    mut v_a_4440_: *mut crate::leanh::LeanObject,
    mut v_a_4441_: *mut crate::leanh::LeanObject,
    mut v_a_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4448_: u8 = 0;
    let mut v_val_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v_val_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_a_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_lhsExpr_4433_);
                v___x_4444_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_lhsExpr_4433_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
                if crate::leanh::lean_obj_tag(v___x_4444_) == 0 {
                    v_a_4445_ = crate::leanh::lean_ctor_get(v___x_4444_, 0);
                    v_isSharedCheck_4489_ = (!crate::leanh::lean_is_exclusive(v___x_4444_)) as u8;
                    if v_isSharedCheck_4489_ == 0 {
                        v___x_4447_ = v___x_4444_;
                        v_isShared_4448_ = v_isSharedCheck_4489_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4445_);
                        crate::leanh::lean_dec(v___x_4444_);
                        v___x_4447_ = crate::leanh::lean_box(0);
                        v_isShared_4448_ = v_isSharedCheck_4489_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4436_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_4434_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_4433_);
                    return v___x_4444_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4445_) == 1 {
                    crate::leanh::lean_del_object(v___x_4447_);
                    v_val_4449_ = crate::leanh::lean_ctor_get(v_a_4445_, 0);
                    crate::leanh::lean_inc(v_val_4449_);
                    crate::leanh::lean_dec_ref_known(v_a_4445_, 1);
                    crate::leanh::lean_inc_ref(v_rhsExpr_4434_);
                    v___x_4450_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_rhsExpr_4434_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
                    if crate::leanh::lean_obj_tag(v___x_4450_) == 0 {
                        v_a_4451_ = crate::leanh::lean_ctor_get(v___x_4450_, 0);
                        v_isSharedCheck_4484_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4450_)) as u8;
                        if v_isSharedCheck_4484_ == 0 {
                            v___x_4453_ = v___x_4450_;
                            v_isShared_4454_ = v_isSharedCheck_4484_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4451_);
                            crate::leanh::lean_dec(v___x_4450_);
                            v___x_4453_ = crate::leanh::lean_box(0);
                            v_isShared_4454_ = v_isSharedCheck_4484_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4449_);
                        crate::leanh::lean_dec_ref(v_origExpr_4436_);
                        crate::leanh::lean_dec_ref(v_rhsExpr_4434_);
                        crate::leanh::lean_dec_ref(v_lhsExpr_4433_);
                        return v___x_4450_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4445_);
                    crate::leanh::lean_dec_ref(v_origExpr_4436_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_4434_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_4433_);
                    v___x_4485_ = crate::leanh::lean_box(0);
                    if v_isShared_4448_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4447_, 0, v___x_4485_);
                        v___x_4487_ = v___x_4447_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
                        v___x_4487_ = v_reuseFailAlloc_4488_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4451_) == 1 {
                    crate::leanh::lean_del_object(v___x_4453_);
                    v_val_4455_ = crate::leanh::lean_ctor_get(v_a_4451_, 0);
                    v_isSharedCheck_4479_ = (!crate::leanh::lean_is_exclusive(v_a_4451_)) as u8;
                    if v_isSharedCheck_4479_ == 0 {
                        v___x_4457_ = v_a_4451_;
                        v_isShared_4458_ = v_isSharedCheck_4479_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4455_);
                        crate::leanh::lean_dec(v_a_4451_);
                        v___x_4457_ = crate::leanh::lean_box(0);
                        v_isShared_4458_ = v_isSharedCheck_4479_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4451_);
                    crate::leanh::lean_dec(v_val_4449_);
                    crate::leanh::lean_dec_ref(v_origExpr_4436_);
                    crate::leanh::lean_dec_ref(v_rhsExpr_4434_);
                    crate::leanh::lean_dec_ref(v_lhsExpr_4433_);
                    v___x_4480_ = crate::leanh::lean_box(0);
                    if v_isShared_4454_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4453_, 0, v___x_4480_);
                        v___x_4482_ = v___x_4453_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
                        v___x_4482_ = v_reuseFailAlloc_4483_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4459_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(
                    v_val_4449_,
                    v_val_4455_,
                    v_lhsExpr_4433_,
                    v_rhsExpr_4434_,
                    v_gate_4435_,
                    v_origExpr_4436_,
                );
                if crate::leanh::lean_obj_tag(v___x_4459_) == 0 {
                    v_a_4460_ = crate::leanh::lean_ctor_get(v___x_4459_, 0);
                    v_isSharedCheck_4470_ = (!crate::leanh::lean_is_exclusive(v___x_4459_)) as u8;
                    if v_isSharedCheck_4470_ == 0 {
                        v___x_4462_ = v___x_4459_;
                        v_isShared_4463_ = v_isSharedCheck_4470_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4460_);
                        crate::leanh::lean_dec(v___x_4459_);
                        v___x_4462_ = crate::leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4470_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4457_);
                    v_a_4471_ = crate::leanh::lean_ctor_get(v___x_4459_, 0);
                    v_isSharedCheck_4478_ = (!crate::leanh::lean_is_exclusive(v___x_4459_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4473_ = v___x_4459_;
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4471_);
                        crate::leanh::lean_dec(v___x_4459_);
                        v___x_4473_ = crate::leanh::lean_box(0);
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4458_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4457_, 0, v_a_4460_);
                    v___x_4465_ = v___x_4457_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4460_);
                    v___x_4465_ = v_reuseFailAlloc_4469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4462_, 0, v___x_4465_);
                    v___x_4467_ = v___x_4462_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
                    v___x_4467_ = v_reuseFailAlloc_4468_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4467_;
            }
            7 => {
                if v_isShared_4474_ == 0 {
                    v___x_4476_ = v___x_4473_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
                    v___x_4476_ = v_reuseFailAlloc_4477_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4476_;
            }
            9 => {
                return v___x_4482_;
            }
            10 => {
                return v___x_4487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(
    mut v_origExpr_4490_: *mut crate::leanh::LeanObject,
    mut v_a_4491_: *mut crate::leanh::LeanObject,
    mut v_a_4492_: *mut crate::leanh::LeanObject,
    mut v_a_4493_: *mut crate::leanh::LeanObject,
    mut v_a_4494_: *mut crate::leanh::LeanObject,
    mut v_a_4495_: *mut crate::leanh::LeanObject,
    mut v_a_4496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: u8 = 0;
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: u8 = 0;
    let mut v___x_4510_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: u8 = 0;
    let mut v___x_4516_: u8 = 0;
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: u8 = 0;
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: u8 = 0;
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: u8 = 0;
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: u8 = 0;
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4556_: u8 = 0;
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4561_: u8 = 0;
    let mut v_val_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4567_: u8 = 0;
    let mut v_val_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4573_: u8 = 0;
    let mut v_val_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4589_: u8 = 0;
    let mut v_a_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4597_: u8 = 0;
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v___x_4614_: u8 = 0;
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v_val_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4638_: u8 = 0;
    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut v_isSharedCheck_4647_: u8 = 0;
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4657_: u8 = 0;
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_a_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4676_: u8 = 0;
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut v_a_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_a_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v_a_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4501_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0;
                v___x_4502_ = l_Lean_Core_checkSystem(v___x_4501_, v_a_4495_, v_a_4496_);
                if crate::leanh::lean_obj_tag(v___x_4502_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4502_, 1);
                    crate::leanh::lean_inc_ref(v_origExpr_4490_);
                    v___x_4503_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_4490_, v_a_4494_);
                    if crate::leanh::lean_obj_tag(v___x_4503_) == 0 {
                        v_a_4504_ = crate::leanh::lean_ctor_get(v___x_4503_, 0);
                        crate::leanh::lean_inc(v_a_4504_);
                        crate::leanh::lean_dec_ref_known(v___x_4503_, 1);
                        v___x_4505_ = l_Lean_Expr_cleanupAnnotations(v_a_4504_);
                        v___x_4506_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3;
                        v___x_4507_ = l_Lean_Expr_isConstOf(v___x_4505_, v___x_4506_);
                        if v___x_4507_ == 0 {
                            v___x_4508_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5;
                            v___x_4509_ = l_Lean_Expr_isConstOf(v___x_4505_, v___x_4508_);
                            if v___x_4509_ == 0 {
                                v___x_4510_ = l_Lean_Expr_isApp(v___x_4505_);
                                if v___x_4510_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_4505_);
                                    v___x_4511_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                    return v___x_4511_;
                                } else {
                                    v_arg_4512_ = crate::leanh::lean_ctor_get(v___x_4505_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_4512_);
                                    v___x_4513_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4505_);
                                    v___x_4514_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6;
                                    v___x_4515_ = l_Lean_Expr_isConstOf(v___x_4513_, v___x_4514_);
                                    if v___x_4515_ == 0 {
                                        v___x_4516_ = l_Lean_Expr_isApp(v___x_4513_);
                                        if v___x_4516_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_4513_);
                                            crate::leanh::lean_dec_ref(v_arg_4512_);
                                            v___x_4517_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                            return v___x_4517_;
                                        } else {
                                            v_arg_4518_ =
                                                crate::leanh::lean_ctor_get(v___x_4513_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_4518_);
                                            v___x_4519_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_4513_);
                                            v___x_4520_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7;
                                            v___x_4521_ =
                                                l_Lean_Expr_isConstOf(v___x_4519_, v___x_4520_);
                                            if v___x_4521_ == 0 {
                                                v___x_4522_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8;
                                                v___x_4523_ =
                                                    l_Lean_Expr_isConstOf(v___x_4519_, v___x_4522_);
                                                if v___x_4523_ == 0 {
                                                    v___x_4524_ = l_Lean_Expr_isApp(v___x_4519_);
                                                    if v___x_4524_ == 0 {
                                                        crate::leanh::lean_dec_ref(v___x_4519_);
                                                        crate::leanh::lean_dec_ref(v_arg_4518_);
                                                        crate::leanh::lean_dec_ref(v_arg_4512_);
                                                        v___x_4525_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                        return v___x_4525_;
                                                    } else {
                                                        v_arg_4526_ = crate::leanh::lean_ctor_get(
                                                            v___x_4519_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_arg_4526_);
                                                        v___x_4527_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_4519_,
                                                            );
                                                        v___x_4528_ =
                                                            l_Lean_Expr_isApp(v___x_4527_);
                                                        if v___x_4528_ == 0 {
                                                            crate::leanh::lean_dec_ref(v___x_4527_);
                                                            crate::leanh::lean_dec_ref(v_arg_4526_);
                                                            crate::leanh::lean_dec_ref(v_arg_4518_);
                                                            crate::leanh::lean_dec_ref(v_arg_4512_);
                                                            v___x_4529_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                            return v___x_4529_;
                                                        } else {
                                                            v_arg_4530_ =
                                                                crate::leanh::lean_ctor_get(
                                                                    v___x_4527_,
                                                                    1,
                                                                );
                                                            crate::leanh::lean_inc_ref(v_arg_4530_);
                                                            v___x_4531_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_4527_,
                                                                );
                                                            v___x_4532_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10;
                                                            v___x_4533_ = l_Lean_Expr_isConstOf(
                                                                v___x_4531_,
                                                                v___x_4532_,
                                                            );
                                                            if v___x_4533_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_4526_,
                                                                );
                                                                v___x_4534_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7;
                                                                v___x_4535_ = l_Lean_Expr_isConstOf(
                                                                    v___x_4531_,
                                                                    v___x_4534_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_4531_,
                                                                );
                                                                if v___x_4535_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_4530_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_4518_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_4512_,
                                                                    );
                                                                    v___x_4536_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                    return v___x_4536_;
                                                                } else {
                                                                    v___x_4537_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_4530_, v_a_4494_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_4537_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_4538_ = crate::leanh::lean_ctor_get(v___x_4537_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_4538_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_4537_, 1);
                                                                        v___x_4539_ = l_Lean_Expr_cleanupAnnotations(v_a_4538_);
                                                                        v___x_4540_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11;
                                                                        v___x_4541_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_4539_,
                                                                                v___x_4540_,
                                                                            );
                                                                        if v___x_4541_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_4518_);
                                                                            crate::leanh::lean_dec_ref(v_arg_4512_);
                                                                            v___x_4542_ =
                                                                                l_Lean_Expr_isApp(
                                                                                    v___x_4539_,
                                                                                );
                                                                            if v___x_4542_ == 0 {
                                                                                crate::leanh::lean_dec_ref(v___x_4539_);
                                                                                crate::leanh::lean_dec_ref(v_origExpr_4490_);
                                                                                state = 1;
                                                                                continue;
                                                                            } else {
                                                                                v___x_4543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4539_);
                                                                                v___x_4544_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                                                                                v___x_4545_ = l_Lean_Expr_isConstOf(v___x_4543_, v___x_4544_);
                                                                                crate::leanh::lean_dec_ref(v___x_4543_);
                                                                                if v___x_4545_ == 0
                                                                                {
                                                                                    crate::leanh::lean_dec_ref(v_origExpr_4490_);
                                                                                    state = 1;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_4546_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                                    return v___x_4546_;
                                                                                }
                                                                            }
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v___x_4539_);
                                                                            v___x_4547_ = 2;
                                                                            v___x_4548_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_4518_, v_arg_4512_, v___x_4547_, v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                            return v___x_4548_;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_4518_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_4512_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_origExpr_4490_,
                                                                        );
                                                                        v_a_4549_ = crate::leanh::lean_ctor_get(v___x_4537_, 0);
                                                                        v_isSharedCheck_4556_ = (!crate::leanh::lean_is_exclusive(v___x_4537_)) as u8;
                                                                        if v_isSharedCheck_4556_
                                                                            == 0
                                                                        {
                                                                            v___x_4551_ =
                                                                                v___x_4537_;
                                                                            v_isShared_4552_ = v_isSharedCheck_4556_;
                                                                            state = 2;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_4549_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_4537_,
                                                                            );
                                                                            v___x_4551_ = crate::leanh::lean_box(0);
                                                                            v_isShared_4552_ = v_isSharedCheck_4556_;
                                                                            state = 2;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_4531_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_4530_,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_4526_,
                                                                );
                                                                v___x_4557_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4526_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_4557_,
                                                                ) == 0
                                                                {
                                                                    v_a_4558_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_4557_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4613_ = (!crate::leanh::lean_is_exclusive(v___x_4557_)) as u8;
                                                                    if v_isSharedCheck_4613_ == 0 {
                                                                        v___x_4560_ = v___x_4557_;
                                                                        v_isShared_4561_ =
                                                                            v_isSharedCheck_4613_;
                                                                        state = 4;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_4558_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_4557_,
                                                                        );
                                                                        v___x_4560_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_4561_ =
                                                                            v_isSharedCheck_4613_;
                                                                        state = 4;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_4526_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_4518_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_4512_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_origExpr_4490_,
                                                                    );
                                                                    return v___x_4557_;
                                                                }
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_4519_);
                                                    v___x_4614_ = 0;
                                                    v___x_4615_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_4518_, v_arg_4512_, v___x_4614_, v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                    return v___x_4615_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_4519_);
                                                v___x_4616_ = 1;
                                                v___x_4617_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_4518_, v_arg_4512_, v___x_4616_, v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                return v___x_4617_;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_4513_);
                                        crate::leanh::lean_inc_ref(v_arg_4512_);
                                        v___x_4618_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4512_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                        if crate::leanh::lean_obj_tag(v___x_4618_) == 0 {
                                            v_a_4619_ = crate::leanh::lean_ctor_get(v___x_4618_, 0);
                                            v_isSharedCheck_4652_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4618_))
                                                    as u8;
                                            if v_isSharedCheck_4652_ == 0 {
                                                v___x_4621_ = v___x_4618_;
                                                v_isShared_4622_ = v_isSharedCheck_4652_;
                                                state = 16;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_4619_);
                                                crate::leanh::lean_dec(v___x_4618_);
                                                v___x_4621_ = crate::leanh::lean_box(0);
                                                v_isShared_4622_ = v_isSharedCheck_4652_;
                                                state = 16;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_arg_4512_);
                                            crate::leanh::lean_dec_ref(v_origExpr_4490_);
                                            return v___x_4618_;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4505_);
                                crate::leanh::lean_dec_ref(v_origExpr_4490_);
                                v___x_4653_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v___x_4509_);
                                if crate::leanh::lean_obj_tag(v___x_4653_) == 0 {
                                    v_a_4654_ = crate::leanh::lean_ctor_get(v___x_4653_, 0);
                                    v_isSharedCheck_4662_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4653_)) as u8;
                                    if v_isSharedCheck_4662_ == 0 {
                                        v___x_4656_ = v___x_4653_;
                                        v_isShared_4657_ = v_isSharedCheck_4662_;
                                        state = 24;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4654_);
                                        crate::leanh::lean_dec(v___x_4653_);
                                        v___x_4656_ = crate::leanh::lean_box(0);
                                        v_isShared_4657_ = v_isSharedCheck_4662_;
                                        state = 24;
                                        continue;
                                    }
                                } else {
                                    v_a_4663_ = crate::leanh::lean_ctor_get(v___x_4653_, 0);
                                    v_isSharedCheck_4670_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4653_)) as u8;
                                    if v_isSharedCheck_4670_ == 0 {
                                        v___x_4665_ = v___x_4653_;
                                        v_isShared_4666_ = v_isSharedCheck_4670_;
                                        state = 26;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4663_);
                                        crate::leanh::lean_dec(v___x_4653_);
                                        v___x_4665_ = crate::leanh::lean_box(0);
                                        v_isShared_4666_ = v_isSharedCheck_4670_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4505_);
                            crate::leanh::lean_dec_ref(v_origExpr_4490_);
                            v___x_4671_ = 0;
                            v___x_4672_ =
                                l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(
                                    v___x_4671_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_4672_) == 0 {
                                v_a_4673_ = crate::leanh::lean_ctor_get(v___x_4672_, 0);
                                v_isSharedCheck_4681_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4672_)) as u8;
                                if v_isSharedCheck_4681_ == 0 {
                                    v___x_4675_ = v___x_4672_;
                                    v_isShared_4676_ = v_isSharedCheck_4681_;
                                    state = 28;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4673_);
                                    crate::leanh::lean_dec(v___x_4672_);
                                    v___x_4675_ = crate::leanh::lean_box(0);
                                    v_isShared_4676_ = v_isSharedCheck_4681_;
                                    state = 28;
                                    continue;
                                }
                            } else {
                                v_a_4682_ = crate::leanh::lean_ctor_get(v___x_4672_, 0);
                                v_isSharedCheck_4689_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4672_)) as u8;
                                if v_isSharedCheck_4689_ == 0 {
                                    v___x_4684_ = v___x_4672_;
                                    v_isShared_4685_ = v_isSharedCheck_4689_;
                                    state = 30;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4682_);
                                    crate::leanh::lean_dec(v___x_4672_);
                                    v___x_4684_ = crate::leanh::lean_box(0);
                                    v_isShared_4685_ = v_isSharedCheck_4689_;
                                    state = 30;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_origExpr_4490_);
                        v_a_4690_ = crate::leanh::lean_ctor_get(v___x_4503_, 0);
                        v_isSharedCheck_4697_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4503_)) as u8;
                        if v_isSharedCheck_4697_ == 0 {
                            v___x_4692_ = v___x_4503_;
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4690_);
                            crate::leanh::lean_dec(v___x_4503_);
                            v___x_4692_ = crate::leanh::lean_box(0);
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4490_);
                    v_a_4698_ = crate::leanh::lean_ctor_get(v___x_4502_, 0);
                    v_isSharedCheck_4705_ = (!crate::leanh::lean_is_exclusive(v___x_4502_)) as u8;
                    if v_isSharedCheck_4705_ == 0 {
                        v___x_4700_ = v___x_4502_;
                        v_isShared_4701_ = v_isSharedCheck_4705_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4698_);
                        crate::leanh::lean_dec(v___x_4502_);
                        v___x_4700_ = crate::leanh::lean_box(0);
                        v_isShared_4701_ = v_isSharedCheck_4705_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4499_ = crate::leanh::lean_box(0);
                v___x_4500_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4500_, 0, v___x_4499_);
                return v___x_4500_;
            }
            2 => {
                if v_isShared_4552_ == 0 {
                    v___x_4554_ = v___x_4551_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4555_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
                    v___x_4554_ = v_reuseFailAlloc_4555_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4554_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_4558_) == 1 {
                    crate::leanh::lean_del_object(v___x_4560_);
                    v_val_4562_ = crate::leanh::lean_ctor_get(v_a_4558_, 0);
                    crate::leanh::lean_inc(v_val_4562_);
                    crate::leanh::lean_dec_ref_known(v_a_4558_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4518_);
                    v___x_4563_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4518_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                    if crate::leanh::lean_obj_tag(v___x_4563_) == 0 {
                        v_a_4564_ = crate::leanh::lean_ctor_get(v___x_4563_, 0);
                        v_isSharedCheck_4608_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4563_)) as u8;
                        if v_isSharedCheck_4608_ == 0 {
                            v___x_4566_ = v___x_4563_;
                            v_isShared_4567_ = v_isSharedCheck_4608_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4564_);
                            crate::leanh::lean_dec(v___x_4563_);
                            v___x_4566_ = crate::leanh::lean_box(0);
                            v_isShared_4567_ = v_isSharedCheck_4608_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4562_);
                        crate::leanh::lean_dec_ref(v_arg_4526_);
                        crate::leanh::lean_dec_ref(v_arg_4518_);
                        crate::leanh::lean_dec_ref(v_arg_4512_);
                        crate::leanh::lean_dec_ref(v_origExpr_4490_);
                        return v___x_4563_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4558_);
                    crate::leanh::lean_dec_ref(v_arg_4526_);
                    crate::leanh::lean_dec_ref(v_arg_4518_);
                    crate::leanh::lean_dec_ref(v_arg_4512_);
                    crate::leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4609_ = crate::leanh::lean_box(0);
                    if v_isShared_4561_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4609_);
                        v___x_4611_ = v___x_4560_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
                        v___x_4611_ = v_reuseFailAlloc_4612_;
                        state = 15;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4564_) == 1 {
                    crate::leanh::lean_del_object(v___x_4566_);
                    v_val_4568_ = crate::leanh::lean_ctor_get(v_a_4564_, 0);
                    crate::leanh::lean_inc(v_val_4568_);
                    crate::leanh::lean_dec_ref_known(v_a_4564_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4512_);
                    v___x_4569_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4512_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                    if crate::leanh::lean_obj_tag(v___x_4569_) == 0 {
                        v_a_4570_ = crate::leanh::lean_ctor_get(v___x_4569_, 0);
                        v_isSharedCheck_4603_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4569_)) as u8;
                        if v_isSharedCheck_4603_ == 0 {
                            v___x_4572_ = v___x_4569_;
                            v_isShared_4573_ = v_isSharedCheck_4603_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4570_);
                            crate::leanh::lean_dec(v___x_4569_);
                            v___x_4572_ = crate::leanh::lean_box(0);
                            v_isShared_4573_ = v_isSharedCheck_4603_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4568_);
                        crate::leanh::lean_dec(v_val_4562_);
                        crate::leanh::lean_dec_ref(v_arg_4526_);
                        crate::leanh::lean_dec_ref(v_arg_4518_);
                        crate::leanh::lean_dec_ref(v_arg_4512_);
                        crate::leanh::lean_dec_ref(v_origExpr_4490_);
                        return v___x_4569_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4564_);
                    crate::leanh::lean_dec(v_val_4562_);
                    crate::leanh::lean_dec_ref(v_arg_4526_);
                    crate::leanh::lean_dec_ref(v_arg_4518_);
                    crate::leanh::lean_dec_ref(v_arg_4512_);
                    crate::leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4604_ = crate::leanh::lean_box(0);
                    if v_isShared_4567_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4566_, 0, v___x_4604_);
                        v___x_4606_ = v___x_4566_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4607_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
                        v___x_4606_ = v_reuseFailAlloc_4607_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_4570_) == 1 {
                    crate::leanh::lean_del_object(v___x_4572_);
                    v_val_4574_ = crate::leanh::lean_ctor_get(v_a_4570_, 0);
                    v_isSharedCheck_4598_ = (!crate::leanh::lean_is_exclusive(v_a_4570_)) as u8;
                    if v_isSharedCheck_4598_ == 0 {
                        v___x_4576_ = v_a_4570_;
                        v_isShared_4577_ = v_isSharedCheck_4598_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4574_);
                        crate::leanh::lean_dec(v_a_4570_);
                        v___x_4576_ = crate::leanh::lean_box(0);
                        v_isShared_4577_ = v_isSharedCheck_4598_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4570_);
                    crate::leanh::lean_dec(v_val_4568_);
                    crate::leanh::lean_dec(v_val_4562_);
                    crate::leanh::lean_dec_ref(v_arg_4526_);
                    crate::leanh::lean_dec_ref(v_arg_4518_);
                    crate::leanh::lean_dec_ref(v_arg_4512_);
                    crate::leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4599_ = crate::leanh::lean_box(0);
                    if v_isShared_4573_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4572_, 0, v___x_4599_);
                        v___x_4601_ = v___x_4572_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4602_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
                        v___x_4601_ = v_reuseFailAlloc_4602_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v___x_4578_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(
                    v_val_4562_,
                    v_val_4568_,
                    v_val_4574_,
                    v_arg_4526_,
                    v_arg_4518_,
                    v_arg_4512_,
                    v_origExpr_4490_,
                );
                if crate::leanh::lean_obj_tag(v___x_4578_) == 0 {
                    v_a_4579_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                    v_isSharedCheck_4589_ = (!crate::leanh::lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4589_ == 0 {
                        v___x_4581_ = v___x_4578_;
                        v_isShared_4582_ = v_isSharedCheck_4589_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4579_);
                        crate::leanh::lean_dec(v___x_4578_);
                        v___x_4581_ = crate::leanh::lean_box(0);
                        v_isShared_4582_ = v_isSharedCheck_4589_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4576_);
                    v_a_4590_ = crate::leanh::lean_ctor_get(v___x_4578_, 0);
                    v_isSharedCheck_4597_ = (!crate::leanh::lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4597_ == 0 {
                        v___x_4592_ = v___x_4578_;
                        v_isShared_4593_ = v_isSharedCheck_4597_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4590_);
                        crate::leanh::lean_dec(v___x_4578_);
                        v___x_4592_ = crate::leanh::lean_box(0);
                        v_isShared_4593_ = v_isSharedCheck_4597_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4576_, 0, v_a_4579_);
                    v___x_4584_ = v___x_4576_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4588_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4579_);
                    v___x_4584_ = v_reuseFailAlloc_4588_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4581_, 0, v___x_4584_);
                    v___x_4586_ = v___x_4581_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 0, v___x_4584_);
                    v___x_4586_ = v_reuseFailAlloc_4587_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4586_;
            }
            11 => {
                if v_isShared_4593_ == 0 {
                    v___x_4595_ = v___x_4592_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4596_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
                    v___x_4595_ = v_reuseFailAlloc_4596_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4595_;
            }
            13 => {
                return v___x_4601_;
            }
            14 => {
                return v___x_4606_;
            }
            15 => {
                return v___x_4611_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_a_4619_) == 1 {
                    crate::leanh::lean_del_object(v___x_4621_);
                    v_val_4623_ = crate::leanh::lean_ctor_get(v_a_4619_, 0);
                    v_isSharedCheck_4647_ = (!crate::leanh::lean_is_exclusive(v_a_4619_)) as u8;
                    if v_isSharedCheck_4647_ == 0 {
                        v___x_4625_ = v_a_4619_;
                        v_isShared_4626_ = v_isSharedCheck_4647_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4623_);
                        crate::leanh::lean_dec(v_a_4619_);
                        v___x_4625_ = crate::leanh::lean_box(0);
                        v_isShared_4626_ = v_isSharedCheck_4647_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4619_);
                    crate::leanh::lean_dec_ref(v_arg_4512_);
                    crate::leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4648_ = crate::leanh::lean_box(0);
                    if v_isShared_4622_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4621_, 0, v___x_4648_);
                        v___x_4650_ = v___x_4621_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_4651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
                        v___x_4650_ = v_reuseFailAlloc_4651_;
                        state = 23;
                        continue;
                    }
                }
            }
            17 => {
                v___x_4627_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(
                    v_val_4623_,
                    v_arg_4512_,
                    v_origExpr_4490_,
                );
                if crate::leanh::lean_obj_tag(v___x_4627_) == 0 {
                    v_a_4628_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4638_ = (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4638_ == 0 {
                        v___x_4630_ = v___x_4627_;
                        v_isShared_4631_ = v_isSharedCheck_4638_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4628_);
                        crate::leanh::lean_dec(v___x_4627_);
                        v___x_4630_ = crate::leanh::lean_box(0);
                        v_isShared_4631_ = v_isSharedCheck_4638_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4625_);
                    v_a_4639_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4646_ = (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4646_ == 0 {
                        v___x_4641_ = v___x_4627_;
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4639_);
                        crate::leanh::lean_dec(v___x_4627_);
                        v___x_4641_ = crate::leanh::lean_box(0);
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4626_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4625_, 0, v_a_4628_);
                    v___x_4633_ = v___x_4625_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4628_);
                    v___x_4633_ = v_reuseFailAlloc_4637_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4630_, 0, v___x_4633_);
                    v___x_4635_ = v___x_4630_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
                    v___x_4635_ = v_reuseFailAlloc_4636_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4635_;
            }
            21 => {
                if v_isShared_4642_ == 0 {
                    v___x_4644_ = v___x_4641_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
                    v___x_4644_ = v_reuseFailAlloc_4645_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4644_;
            }
            23 => {
                return v___x_4650_;
            }
            24 => {
                v___x_4658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4658_, 0, v_a_4654_);
                if v_isShared_4657_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4656_, 0, v___x_4658_);
                    v___x_4660_ = v___x_4656_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
                    v___x_4660_ = v_reuseFailAlloc_4661_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4660_;
            }
            26 => {
                if v_isShared_4666_ == 0 {
                    v___x_4668_ = v___x_4665_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
                    v___x_4668_ = v_reuseFailAlloc_4669_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4668_;
            }
            28 => {
                v___x_4677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4677_, 0, v_a_4673_);
                if v_isShared_4676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4675_, 0, v___x_4677_);
                    v___x_4679_ = v___x_4675_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
                    v___x_4679_ = v_reuseFailAlloc_4680_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4679_;
            }
            30 => {
                if v_isShared_4685_ == 0 {
                    v___x_4687_ = v___x_4684_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
                    v___x_4687_ = v_reuseFailAlloc_4688_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4687_;
            }
            32 => {
                if v_isShared_4693_ == 0 {
                    v___x_4695_ = v___x_4692_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
                    v___x_4695_ = v_reuseFailAlloc_4696_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4695_;
            }
            34 => {
                if v_isShared_4701_ == 0 {
                    v___x_4703_ = v___x_4700_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
                    v___x_4703_ = v_reuseFailAlloc_4704_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(
    mut v_e_4706_: *mut crate::leanh::LeanObject,
    mut v_a_4707_: *mut crate::leanh::LeanObject,
    mut v_a_4708_: *mut crate::leanh::LeanObject,
    mut v_a_4709_: *mut crate::leanh::LeanObject,
    mut v_a_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4738_ = lean_st_ref_get(v_a_4707_);
                v_bvLogicalCache_4739_ = crate::leanh::lean_ctor_get(v___x_4738_, 3);
                crate::leanh::lean_inc_ref(v_bvLogicalCache_4739_);
                crate::leanh::lean_dec(v___x_4738_);
                v___x_4740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvLogicalCache_4739_, v_e_4706_);
                crate::leanh::lean_dec_ref(v_bvLogicalCache_4739_);
                if crate::leanh::lean_obj_tag(v___x_4740_) == 0 {
                    crate::leanh::lean_inc_ref(v_e_4706_);
                    v___x_4741_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_e_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
                    if crate::leanh::lean_obj_tag(v___x_4741_) == 0 {
                        v_a_4742_ = crate::leanh::lean_ctor_get(v___x_4741_, 0);
                        crate::leanh::lean_inc(v_a_4742_);
                        if crate::leanh::lean_obj_tag(v_a_4742_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4741_, 1);
                            crate::leanh::lean_inc_ref(v_e_4706_);
                            v___x_4743_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(
                                v_e_4706_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_,
                            );
                            v___y_4715_ = v___x_4743_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_4742_, 1);
                            v___y_4715_ = v___x_4741_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_4715_ = v___x_4741_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4706_);
                    v_val_4744_ = crate::leanh::lean_ctor_get(v___x_4740_, 0);
                    v_isSharedCheck_4751_ = (!crate::leanh::lean_is_exclusive(v___x_4740_)) as u8;
                    if v_isSharedCheck_4751_ == 0 {
                        v___x_4746_ = v___x_4740_;
                        v_isShared_4747_ = v_isSharedCheck_4751_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4744_);
                        crate::leanh::lean_dec(v___x_4740_);
                        v___x_4746_ = crate::leanh::lean_box(0);
                        v_isShared_4747_ = v_isSharedCheck_4751_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4715_) == 0 {
                    v_a_4716_ = crate::leanh::lean_ctor_get(v___y_4715_, 0);
                    v_isSharedCheck_4737_ = (!crate::leanh::lean_is_exclusive(v___y_4715_)) as u8;
                    if v_isSharedCheck_4737_ == 0 {
                        v___x_4718_ = v___y_4715_;
                        v_isShared_4719_ = v_isSharedCheck_4737_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4716_);
                        crate::leanh::lean_dec(v___y_4715_);
                        v___x_4718_ = crate::leanh::lean_box(0);
                        v_isShared_4719_ = v_isSharedCheck_4737_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4706_);
                    return v___y_4715_;
                }
            }
            2 => {
                v___x_4720_ = lean_st_ref_take(v_a_4707_);
                v_lemmas_4721_ = crate::leanh::lean_ctor_get(v___x_4720_, 0);
                v_bvExprCache_4722_ = crate::leanh::lean_ctor_get(v___x_4720_, 1);
                v_bvPredCache_4723_ = crate::leanh::lean_ctor_get(v___x_4720_, 2);
                v_bvLogicalCache_4724_ = crate::leanh::lean_ctor_get(v___x_4720_, 3);
                v_isSharedCheck_4736_ = (!crate::leanh::lean_is_exclusive(v___x_4720_)) as u8;
                if v_isSharedCheck_4736_ == 0 {
                    v___x_4726_ = v___x_4720_;
                    v_isShared_4727_ = v_isSharedCheck_4736_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bvLogicalCache_4724_);
                    crate::leanh::lean_inc(v_bvPredCache_4723_);
                    crate::leanh::lean_inc(v_bvExprCache_4722_);
                    crate::leanh::lean_inc(v_lemmas_4721_);
                    crate::leanh::lean_dec(v___x_4720_);
                    v___x_4726_ = crate::leanh::lean_box(0);
                    v_isShared_4727_ = v_isSharedCheck_4736_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_4716_);
                v___x_4728_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvLogicalCache_4724_, v_e_4706_, v_a_4716_);
                if v_isShared_4727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4726_, 3, v___x_4728_);
                    v___x_4730_ = v___x_4726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_lemmas_4721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 1, v_bvExprCache_4722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 2, v_bvPredCache_4723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 3, v___x_4728_);
                    v___x_4730_ = v_reuseFailAlloc_4735_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4731_ = lean_st_ref_set(v_a_4707_, v___x_4730_);
                if v_isShared_4719_ == 0 {
                    v___x_4733_ = v___x_4718_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4716_);
                    v___x_4733_ = v_reuseFailAlloc_4734_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4733_;
            }
            6 => {
                if v_isShared_4747_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4746_, 0);
                    v___x_4749_ = v___x_4746_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_val_4744_);
                    v___x_4749_ = v_reuseFailAlloc_4750_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(
    mut v_origExpr_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4760_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_origExpr_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
    return v___x_4760_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(
    mut v_origExpr_4761_: *mut crate::leanh::LeanObject,
    mut v_a_4762_: *mut crate::leanh::LeanObject,
    mut v_a_4763_: *mut crate::leanh::LeanObject,
    mut v_a_4764_: *mut crate::leanh::LeanObject,
    mut v_a_4765_: *mut crate::leanh::LeanObject,
    mut v_a_4766_: *mut crate::leanh::LeanObject,
    mut v_a_4767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4769_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
    return v___x_4769_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4785_ = crate::leanh::lean_box(0);
    v___x_4786_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5;
    v___x_4787_ = l_Lean_mkConst(v___x_4786_, v___x_4785_);
    return v___x_4787_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4795_ = crate::leanh::lean_box(0);
    v___x_4796_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2;
    v___x_4797_ = l_Lean_mkConst(v___x_4796_, v___x_4795_);
    return v___x_4797_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = crate::leanh::lean_box(0);
    v___x_4805_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5;
    v___x_4806_ = l_Lean_mkConst(v___x_4805_, v___x_4804_);
    return v___x_4806_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4813_ = crate::leanh::lean_box(0);
    v___x_4814_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8;
    v___x_4815_ = l_Lean_mkConst(v___x_4814_, v___x_4813_);
    return v___x_4815_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ = crate::leanh::lean_box(0);
    v___x_4824_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11;
    v___x_4825_ = l_Lean_mkConst(v___x_4824_, v___x_4823_);
    return v___x_4825_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = crate::leanh::lean_box(0);
    v___x_4833_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14;
    v___x_4834_ = l_Lean_mkConst(v___x_4833_, v___x_4832_);
    return v___x_4834_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4841_ = crate::leanh::lean_box(0);
    v___x_4842_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17;
    v___x_4843_ = l_Lean_mkConst(v___x_4842_, v___x_4841_);
    return v___x_4843_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4850_ = crate::leanh::lean_box(0);
    v___x_4851_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20;
    v___x_4852_ = l_Lean_mkConst(v___x_4851_, v___x_4850_);
    return v___x_4852_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(
    mut v_innerExpr_4853_: *mut crate::leanh::LeanObject,
    mut v_op_4854_: *mut crate::leanh::LeanObject,
    mut v_congrThm_4855_: *mut crate::leanh::LeanObject,
    mut v_origExpr_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
    mut v_a_4862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v_val_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v_width_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_innerExpr_4853_);
                v___x_4864_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4853_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
                if crate::leanh::lean_obj_tag(v___x_4864_) == 0 {
                    v_a_4865_ = crate::leanh::lean_ctor_get(v___x_4864_, 0);
                    v_isSharedCheck_4913_ = (!crate::leanh::lean_is_exclusive(v___x_4864_)) as u8;
                    if v_isSharedCheck_4913_ == 0 {
                        v___x_4867_ = v___x_4864_;
                        v_isShared_4868_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4865_);
                        crate::leanh::lean_dec(v___x_4864_);
                        v___x_4867_ = crate::leanh::lean_box(0);
                        v_isShared_4868_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4856_);
                    crate::leanh::lean_dec(v_congrThm_4855_);
                    crate::leanh::lean_dec(v_op_4854_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4853_);
                    return v___x_4864_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4865_) == 1 {
                    v_val_4869_ = crate::leanh::lean_ctor_get(v_a_4865_, 0);
                    v_isSharedCheck_4908_ = (!crate::leanh::lean_is_exclusive(v_a_4865_)) as u8;
                    if v_isSharedCheck_4908_ == 0 {
                        v___x_4871_ = v_a_4865_;
                        v_isShared_4872_ = v_isSharedCheck_4908_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4869_);
                        crate::leanh::lean_dec(v_a_4865_);
                        v___x_4871_ = crate::leanh::lean_box(0);
                        v_isShared_4872_ = v_isSharedCheck_4908_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4865_);
                    crate::leanh::lean_dec_ref(v_origExpr_4856_);
                    crate::leanh::lean_dec(v_congrThm_4855_);
                    crate::leanh::lean_dec(v_op_4854_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4853_);
                    v___x_4909_ = crate::leanh::lean_box(0);
                    if v_isShared_4868_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4867_, 0, v___x_4909_);
                        v___x_4911_ = v___x_4867_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
                        v___x_4911_ = v_reuseFailAlloc_4912_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_width_4873_ = crate::leanh::lean_ctor_get(v_val_4869_, 0);
                crate::leanh::lean_inc_n(v_width_4873_, 3);
                v_bvExpr_4874_ = crate::leanh::lean_ctor_get(v_val_4869_, 1);
                v_expr_4875_ = crate::leanh::lean_ctor_get(v_val_4869_, 4);
                crate::leanh::lean_inc_ref(v_bvExpr_4874_);
                crate::leanh::lean_inc(v_op_4854_);
                v___x_4876_ = l_Std_Tactic_BVDecide_BVExpr_un___override(
                    v_width_4873_,
                    v_op_4854_,
                    v_bvExpr_4874_,
                );
                v___x_4877_ = crate::leanh::lean_box(0);
                v___x_4878_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
                v___x_4879_ = l_Lean_mkNatLit(v_width_4873_);
                match crate::leanh::lean_obj_tag(v_op_4854_) {
                    0 => {
                        v___x_4892_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3);
                        v___y_4881_ = v___x_4892_;
                        state = 3;
                        continue;
                    }
                    1 => {
                        v_n_4893_ = crate::leanh::lean_ctor_get(v_op_4854_, 0);
                        crate::leanh::lean_inc(v_n_4893_);
                        crate::leanh::lean_dec_ref_known(v_op_4854_, 1);
                        v___x_4894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6);
                        v___x_4895_ = l_Lean_mkNatLit(v_n_4893_);
                        v___x_4896_ = l_Lean_Expr_app___override(v___x_4894_, v___x_4895_);
                        v___y_4881_ = v___x_4896_;
                        state = 3;
                        continue;
                    }
                    2 => {
                        v_n_4897_ = crate::leanh::lean_ctor_get(v_op_4854_, 0);
                        crate::leanh::lean_inc(v_n_4897_);
                        crate::leanh::lean_dec_ref_known(v_op_4854_, 1);
                        v___x_4898_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9);
                        v___x_4899_ = l_Lean_mkNatLit(v_n_4897_);
                        v___x_4900_ = l_Lean_Expr_app___override(v___x_4898_, v___x_4899_);
                        v___y_4881_ = v___x_4900_;
                        state = 3;
                        continue;
                    }
                    3 => {
                        v_n_4901_ = crate::leanh::lean_ctor_get(v_op_4854_, 0);
                        crate::leanh::lean_inc(v_n_4901_);
                        crate::leanh::lean_dec_ref_known(v_op_4854_, 1);
                        v___x_4902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12);
                        v___x_4903_ = l_Lean_mkNatLit(v_n_4901_);
                        v___x_4904_ = l_Lean_Expr_app___override(v___x_4902_, v___x_4903_);
                        v___y_4881_ = v___x_4904_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        v___x_4905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15);
                        v___y_4881_ = v___x_4905_;
                        state = 3;
                        continue;
                    }
                    5 => {
                        v___x_4906_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18);
                        v___y_4881_ = v___x_4906_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        v___x_4907_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21);
                        v___y_4881_ = v___x_4907_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_expr_4875_);
                v___x_4882_ = l_Lean_mkApp3(v___x_4878_, v___x_4879_, v___y_4881_, v_expr_4875_);
                v___x_4883_ = l_Lean_mkConst(v_congrThm_4855_, v___x_4877_);
                v___x_4884_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___x_4884_, 0, v_val_4869_);
                crate::leanh::lean_closure_set(v___x_4884_, 1, v_innerExpr_4853_);
                crate::leanh::lean_closure_set(v___x_4884_, 2, v___x_4883_);
                v___x_4885_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4885_, 0, v_width_4873_);
                crate::leanh::lean_ctor_set(v___x_4885_, 1, v___x_4876_);
                crate::leanh::lean_ctor_set(v___x_4885_, 2, v_origExpr_4856_);
                crate::leanh::lean_ctor_set(v___x_4885_, 3, v___x_4884_);
                crate::leanh::lean_ctor_set(v___x_4885_, 4, v___x_4882_);
                if v_isShared_4872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4871_, 0, v___x_4885_);
                    v___x_4887_ = v___x_4871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4885_);
                    v___x_4887_ = v_reuseFailAlloc_4891_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4868_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4867_, 0, v___x_4887_);
                    v___x_4889_ = v___x_4867_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
                    v___x_4889_ = v_reuseFailAlloc_4890_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4889_;
            }
            6 => {
                return v___x_4911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(
    mut v_distance_4923_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_4924_: *mut crate::leanh::LeanObject,
    mut v_shiftOp_4925_: *mut crate::leanh::LeanObject,
    mut v_shiftOpName_4926_: *mut crate::leanh::LeanObject,
    mut v_congrThm_4927_: *mut crate::leanh::LeanObject,
    mut v_origExpr_4928_: *mut crate::leanh::LeanObject,
    mut v_a_4929_: *mut crate::leanh::LeanObject,
    mut v_a_4930_: *mut crate::leanh::LeanObject,
    mut v_a_4931_: *mut crate::leanh::LeanObject,
    mut v_a_4932_: *mut crate::leanh::LeanObject,
    mut v_a_4933_: *mut crate::leanh::LeanObject,
    mut v_a_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4940_: u8 = 0;
    let mut v_val_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v_width_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_innerExpr_4924_);
                v___x_4936_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4924_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
                if crate::leanh::lean_obj_tag(v___x_4936_) == 0 {
                    v_a_4937_ = crate::leanh::lean_ctor_get(v___x_4936_, 0);
                    v_isSharedCheck_4972_ = (!crate::leanh::lean_is_exclusive(v___x_4936_)) as u8;
                    if v_isSharedCheck_4972_ == 0 {
                        v___x_4939_ = v___x_4936_;
                        v_isShared_4940_ = v_isSharedCheck_4972_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4937_);
                        crate::leanh::lean_dec(v___x_4936_);
                        v___x_4939_ = crate::leanh::lean_box(0);
                        v_isShared_4940_ = v_isSharedCheck_4972_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4928_);
                    crate::leanh::lean_dec(v_congrThm_4927_);
                    crate::leanh::lean_dec(v_shiftOpName_4926_);
                    crate::leanh::lean_dec_ref(v_shiftOp_4925_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4924_);
                    crate::leanh::lean_dec(v_distance_4923_);
                    return v___x_4936_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4937_) == 1 {
                    v_val_4941_ = crate::leanh::lean_ctor_get(v_a_4937_, 0);
                    v_isSharedCheck_4967_ = (!crate::leanh::lean_is_exclusive(v_a_4937_)) as u8;
                    if v_isSharedCheck_4967_ == 0 {
                        v___x_4943_ = v_a_4937_;
                        v_isShared_4944_ = v_isSharedCheck_4967_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4941_);
                        crate::leanh::lean_dec(v_a_4937_);
                        v___x_4943_ = crate::leanh::lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4967_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4937_);
                    crate::leanh::lean_dec_ref(v_origExpr_4928_);
                    crate::leanh::lean_dec(v_congrThm_4927_);
                    crate::leanh::lean_dec(v_shiftOpName_4926_);
                    crate::leanh::lean_dec_ref(v_shiftOp_4925_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4924_);
                    crate::leanh::lean_dec(v_distance_4923_);
                    v___x_4968_ = crate::leanh::lean_box(0);
                    if v_isShared_4940_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4939_, 0, v___x_4968_);
                        v___x_4970_ = v___x_4939_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4971_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4968_);
                        v___x_4970_ = v_reuseFailAlloc_4971_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_width_4945_ = crate::leanh::lean_ctor_get(v_val_4941_, 0);
                crate::leanh::lean_inc_n(v_width_4945_, 3);
                v_bvExpr_4946_ = crate::leanh::lean_ctor_get(v_val_4941_, 1);
                v_expr_4947_ = crate::leanh::lean_ctor_get(v_val_4941_, 4);
                crate::leanh::lean_inc(v_distance_4923_);
                v___x_4948_ = crate::leanh::lean_apply_1(v_shiftOp_4925_, v_distance_4923_);
                crate::leanh::lean_inc_ref(v_bvExpr_4946_);
                v___x_4949_ = l_Std_Tactic_BVDecide_BVExpr_un___override(
                    v_width_4945_,
                    v___x_4948_,
                    v_bvExpr_4946_,
                );
                v___x_4950_ = crate::leanh::lean_box(0);
                v___x_4951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
                v___x_4952_ = l_Lean_mkNatLit(v_width_4945_);
                v___x_4953_ = l_Lean_mkConst(v_shiftOpName_4926_, v___x_4950_);
                v___x_4954_ = l_Lean_mkNatLit(v_distance_4923_);
                crate::leanh::lean_inc_ref(v___x_4954_);
                v___x_4955_ = l_Lean_Expr_app___override(v___x_4953_, v___x_4954_);
                crate::leanh::lean_inc_ref(v_expr_4947_);
                v___x_4956_ = l_Lean_mkApp3(v___x_4951_, v___x_4952_, v___x_4955_, v_expr_4947_);
                v___x_4957_ = l_Lean_mkConst(v_congrThm_4927_, v___x_4950_);
                v___x_4958_ = l_Lean_Expr_app___override(v___x_4957_, v___x_4954_);
                v___x_4959_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___x_4959_, 0, v_val_4941_);
                crate::leanh::lean_closure_set(v___x_4959_, 1, v_innerExpr_4924_);
                crate::leanh::lean_closure_set(v___x_4959_, 2, v___x_4958_);
                v___x_4960_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4960_, 0, v_width_4945_);
                crate::leanh::lean_ctor_set(v___x_4960_, 1, v___x_4949_);
                crate::leanh::lean_ctor_set(v___x_4960_, 2, v_origExpr_4928_);
                crate::leanh::lean_ctor_set(v___x_4960_, 3, v___x_4959_);
                crate::leanh::lean_ctor_set(v___x_4960_, 4, v___x_4956_);
                if v_isShared_4944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4943_, 0, v___x_4960_);
                    v___x_4962_ = v___x_4943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4960_);
                    v___x_4962_ = v_reuseFailAlloc_4966_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4939_, 0, v___x_4962_);
                    v___x_4964_ = v___x_4939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4962_);
                    v___x_4964_ = v_reuseFailAlloc_4965_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4964_;
            }
            5 => {
                return v___x_4970_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4979_ = crate::leanh::lean_box(0);
    v___x_4980_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85;
    v___x_4981_ = l_Lean_mkConst(v___x_4980_, v___x_4979_);
    return v___x_4981_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(
    mut v_distanceExpr_4991_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_4992_: *mut crate::leanh::LeanObject,
    mut v_rotateOp_4993_: *mut crate::leanh::LeanObject,
    mut v_rotateOpName_4994_: *mut crate::leanh::LeanObject,
    mut v_congrThm_4995_: *mut crate::leanh::LeanObject,
    mut v_origExpr_4996_: *mut crate::leanh::LeanObject,
    mut v_a_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
    mut v_a_5000_: *mut crate::leanh::LeanObject,
    mut v_a_5001_: *mut crate::leanh::LeanObject,
    mut v_a_5002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v_val_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_a_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5004_ = l_Lean_Meta_getNatValue_x3f(
                    v_distanceExpr_4991_,
                    v_a_4999_,
                    v_a_5000_,
                    v_a_5001_,
                    v_a_5002_,
                );
                if crate::leanh::lean_obj_tag(v___x_5004_) == 0 {
                    v_a_5005_ = crate::leanh::lean_ctor_get(v___x_5004_, 0);
                    v_isSharedCheck_5015_ = (!crate::leanh::lean_is_exclusive(v___x_5004_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_5007_ = v___x_5004_;
                        v_isShared_5008_ = v_isSharedCheck_5015_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5005_);
                        crate::leanh::lean_dec(v___x_5004_);
                        v___x_5007_ = crate::leanh::lean_box(0);
                        v_isShared_5008_ = v_isSharedCheck_5015_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_4996_);
                    crate::leanh::lean_dec(v_congrThm_4995_);
                    crate::leanh::lean_dec(v_rotateOpName_4994_);
                    crate::leanh::lean_dec_ref(v_rotateOp_4993_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4992_);
                    v_a_5016_ = crate::leanh::lean_ctor_get(v___x_5004_, 0);
                    v_isSharedCheck_5023_ = (!crate::leanh::lean_is_exclusive(v___x_5004_)) as u8;
                    if v_isSharedCheck_5023_ == 0 {
                        v___x_5018_ = v___x_5004_;
                        v_isShared_5019_ = v_isSharedCheck_5023_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5016_);
                        crate::leanh::lean_dec(v___x_5004_);
                        v___x_5018_ = crate::leanh::lean_box(0);
                        v_isShared_5019_ = v_isSharedCheck_5023_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5005_) == 1 {
                    crate::leanh::lean_del_object(v___x_5007_);
                    v_val_5009_ = crate::leanh::lean_ctor_get(v_a_5005_, 0);
                    crate::leanh::lean_inc(v_val_5009_);
                    crate::leanh::lean_dec_ref_known(v_a_5005_, 1);
                    v___x_5010_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_5009_, v_innerExpr_4992_, v_rotateOp_4993_, v_rotateOpName_4994_, v_congrThm_4995_, v_origExpr_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
                    return v___x_5010_;
                } else {
                    crate::leanh::lean_dec(v_a_5005_);
                    crate::leanh::lean_dec_ref(v_origExpr_4996_);
                    crate::leanh::lean_dec(v_congrThm_4995_);
                    crate::leanh::lean_dec(v_rotateOpName_4994_);
                    crate::leanh::lean_dec_ref(v_rotateOp_4993_);
                    crate::leanh::lean_dec_ref(v_innerExpr_4992_);
                    v___x_5011_ = crate::leanh::lean_box(0);
                    if v_isShared_5008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5007_, 0, v___x_5011_);
                        v___x_5013_ = v___x_5007_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5014_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5011_);
                        v___x_5013_ = v_reuseFailAlloc_5014_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5013_;
            }
            3 => {
                if v_isShared_5019_ == 0 {
                    v___x_5021_ = v___x_5018_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
                    v___x_5021_ = v_reuseFailAlloc_5022_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(
    mut v_origExpr_5057_: *mut crate::leanh::LeanObject,
    mut v_a_5058_: *mut crate::leanh::LeanObject,
    mut v_a_5059_: *mut crate::leanh::LeanObject,
    mut v_a_5060_: *mut crate::leanh::LeanObject,
    mut v_a_5061_: *mut crate::leanh::LeanObject,
    mut v_a_5062_: *mut crate::leanh::LeanObject,
    mut v_a_5063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5077_: u8 = 0;
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: u8 = 0;
    let mut v_arg_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: u8 = 0;
    let mut v_arg_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: u8 = 0;
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: u8 = 0;
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: u8 = 0;
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: u8 = 0;
    let mut v___x_5099_: u8 = 0;
    let mut v_arg_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: u8 = 0;
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: u8 = 0;
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: u8 = 0;
    let mut v___x_5112_: u8 = 0;
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u8 = 0;
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: u8 = 0;
    let mut v_arg_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: u8 = 0;
    let mut v_arg_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: u8 = 0;
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: u8 = 0;
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: u8 = 0;
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: u8 = 0;
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: u8 = 0;
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: u8 = 0;
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: u8 = 0;
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: u8 = 0;
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut v_arg_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: u8 = 0;
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: u8 = 0;
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v___y_5207_: u8 = 0;
    let mut v_a_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_isSharedCheck_5216_: u8 = 0;
    let mut v_a_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5220_: u8 = 0;
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5224_: u8 = 0;
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    let mut v_arg_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: u8 = 0;
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5264_: u8 = 0;
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v___y_5270_: u8 = 0;
    let mut v_a_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5274_: u8 = 0;
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v_isSharedCheck_5279_: u8 = 0;
    let mut v_a_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5283_: u8 = 0;
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v_val_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v_val_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v_width_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5316_: u8 = 0;
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut v_a_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5337_: u8 = 0;
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5341_: u8 = 0;
    let mut v_isSharedCheck_5342_: u8 = 0;
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5352_: u8 = 0;
    let mut v___f_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v_val_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5367_: u8 = 0;
    let mut v_val_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5373_: u8 = 0;
    let mut v_val_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5377_: u8 = 0;
    let mut v_width_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5397_: u8 = 0;
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5402_: u8 = 0;
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut v_a_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v_a_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v_val_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5439_: u8 = 0;
    let mut v_val_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5445_: u8 = 0;
    let mut v_val_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v_val_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5456_: u8 = 0;
    let mut v___x_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5460_: u8 = 0;
    let mut v_unused_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5465_: u8 = 0;
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5474_: u8 = 0;
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5484_: u8 = 0;
    let mut v_a_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5488_: u8 = 0;
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5492_: u8 = 0;
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5497_: u8 = 0;
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5505_: u8 = 0;
    let mut v_val_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5515_: u8 = 0;
    let mut v_a_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5519_: u8 = 0;
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5523_: u8 = 0;
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v_val_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v_val_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5538_: u8 = 0;
    let mut v_width_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5549_: u8 = 0;
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut v_a_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5570_: u8 = 0;
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5574_: u8 = 0;
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_a_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5584_: u8 = 0;
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5593_: u8 = 0;
    let mut v___f_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5612_: u8 = 0;
    let mut v_a_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5616_: u8 = 0;
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5620_: u8 = 0;
    let mut v_a_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5071_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0;
                v___x_5072_ = l_Lean_Core_checkSystem(v___x_5071_, v_a_5062_, v_a_5063_);
                if crate::leanh::lean_obj_tag(v___x_5072_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5072_, 1);
                    crate::leanh::lean_inc_ref(v_origExpr_5057_);
                    v___x_5073_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_5057_, v_a_5061_);
                    if crate::leanh::lean_obj_tag(v___x_5073_) == 0 {
                        v_a_5074_ = crate::leanh::lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5612_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5612_ == 0 {
                            v___x_5076_ = v___x_5073_;
                            v_isShared_5077_ = v_isSharedCheck_5612_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5074_);
                            crate::leanh::lean_dec(v___x_5073_);
                            v___x_5076_ = crate::leanh::lean_box(0);
                            v_isShared_5077_ = v_isSharedCheck_5612_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5613_ = crate::leanh::lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5620_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5620_ == 0 {
                            v___x_5615_ = v___x_5073_;
                            v_isShared_5616_ = v_isSharedCheck_5620_;
                            state = 83;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5613_);
                            crate::leanh::lean_dec(v___x_5073_);
                            v___x_5615_ = crate::leanh::lean_box(0);
                            v_isShared_5616_ = v_isSharedCheck_5620_;
                            state = 83;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5621_ = crate::leanh::lean_ctor_get(v___x_5072_, 0);
                    v_isSharedCheck_5628_ = (!crate::leanh::lean_is_exclusive(v___x_5072_)) as u8;
                    if v_isSharedCheck_5628_ == 0 {
                        v___x_5623_ = v___x_5072_;
                        v_isShared_5624_ = v_isSharedCheck_5628_;
                        state = 85;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5621_);
                        crate::leanh::lean_dec(v___x_5072_);
                        v___x_5623_ = crate::leanh::lean_box(0);
                        v_isShared_5624_ = v_isSharedCheck_5628_;
                        state = 85;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5066_ = crate::leanh::lean_box(0);
                v___x_5067_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5067_, 0, v___x_5066_);
                return v___x_5067_;
            }
            2 => {
                v___x_5069_ = crate::leanh::lean_box(0);
                v___x_5070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5070_, 0, v___x_5069_);
                return v___x_5070_;
            }
            3 => {
                v___x_5083_ = l_Lean_Expr_cleanupAnnotations(v_a_5074_);
                v___x_5084_ = l_Lean_Expr_isApp(v___x_5083_);
                if v___x_5084_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5083_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 4;
                    continue;
                } else {
                    v_arg_5085_ = crate::leanh::lean_ctor_get(v___x_5083_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5086_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5083_);
                    v___x_5087_ = l_Lean_Expr_isApp(v___x_5086_);
                    if v___x_5087_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5086_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 4;
                        continue;
                    } else {
                        v_arg_5088_ = crate::leanh::lean_ctor_get(v___x_5086_, 1);
                        crate::leanh::lean_inc_ref(v_arg_5088_);
                        v___x_5089_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5086_);
                        v___x_5090_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0;
                        v___x_5091_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0;
                        v___x_5092_ = l_Lean_Expr_isConstOf(v___x_5089_, v___x_5091_);
                        if v___x_5092_ == 0 {
                            v___x_5093_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1;
                            v___x_5094_ = l_Lean_Expr_isConstOf(v___x_5089_, v___x_5093_);
                            if v___x_5094_ == 0 {
                                v___x_5095_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2;
                                v___x_5096_ = l_Lean_Expr_isConstOf(v___x_5089_, v___x_5095_);
                                if v___x_5096_ == 0 {
                                    v___x_5097_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4;
                                    v___x_5098_ = l_Lean_Expr_isConstOf(v___x_5089_, v___x_5097_);
                                    if v___x_5098_ == 0 {
                                        v___x_5099_ = l_Lean_Expr_isApp(v___x_5089_);
                                        if v___x_5099_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_5089_);
                                            crate::leanh::lean_dec_ref(v_arg_5088_);
                                            crate::leanh::lean_dec_ref(v_arg_5085_);
                                            crate::leanh::lean_dec_ref(v_origExpr_5057_);
                                            state = 4;
                                            continue;
                                        } else {
                                            v_arg_5100_ =
                                                crate::leanh::lean_ctor_get(v___x_5089_, 1);
                                            crate::leanh::lean_inc_ref(v_arg_5100_);
                                            v___x_5101_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_5089_);
                                            v___x_5102_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5;
                                            v___x_5103_ =
                                                l_Lean_Expr_isConstOf(v___x_5101_, v___x_5102_);
                                            if v___x_5103_ == 0 {
                                                v___x_5104_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6;
                                                v___x_5105_ =
                                                    l_Lean_Expr_isConstOf(v___x_5101_, v___x_5104_);
                                                if v___x_5105_ == 0 {
                                                    v___x_5106_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8;
                                                    v___x_5107_ = l_Lean_Expr_isConstOf(
                                                        v___x_5101_,
                                                        v___x_5106_,
                                                    );
                                                    if v___x_5107_ == 0 {
                                                        v___x_5108_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10;
                                                        v___x_5109_ = l_Lean_Expr_isConstOf(
                                                            v___x_5101_,
                                                            v___x_5108_,
                                                        );
                                                        if v___x_5109_ == 0 {
                                                            v___x_5110_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13;
                                                            v___x_5111_ = l_Lean_Expr_isConstOf(
                                                                v___x_5101_,
                                                                v___x_5110_,
                                                            );
                                                            if v___x_5111_ == 0 {
                                                                v___x_5112_ =
                                                                    l_Lean_Expr_isApp(v___x_5101_);
                                                                if v___x_5112_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_5101_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_5100_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_5088_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_5085_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_origExpr_5057_,
                                                                    );
                                                                    state = 4;
                                                                    continue;
                                                                } else {
                                                                    v___x_5113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5101_);
                                                                    v___x_5114_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10;
                                                                    v___x_5115_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_5113_,
                                                                            v___x_5114_,
                                                                        );
                                                                    if v___x_5115_ == 0 {
                                                                        v___x_5116_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15;
                                                                        v___x_5117_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_5113_,
                                                                                v___x_5116_,
                                                                            );
                                                                        if v___x_5117_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v_arg_5100_);
                                                                            v___x_5118_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17;
                                                                            v___x_5119_ = l_Lean_Expr_isConstOf(v___x_5113_, v___x_5118_);
                                                                            if v___x_5119_ == 0 {
                                                                                v___x_5120_ = l_Lean_Expr_isApp(v___x_5113_);
                                                                                if v___x_5120_ == 0
                                                                                {
                                                                                    crate::leanh::lean_dec_ref(v___x_5113_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_5088_);
                                                                                    crate::leanh::lean_dec_ref(v_arg_5085_);
                                                                                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                                                                                    state = 4;
                                                                                    continue;
                                                                                } else {
                                                                                    v_arg_5121_ = crate::leanh::lean_ctor_get(v___x_5113_, 1);
                                                                                    crate::leanh::lean_inc_ref(v_arg_5121_);
                                                                                    v___x_5122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5113_);
                                                                                    v___x_5123_ = l_Lean_Expr_isApp(v___x_5122_);
                                                                                    if v___x_5123_
                                                                                        == 0
                                                                                    {
                                                                                        crate::leanh::lean_dec_ref(v___x_5122_);
                                                                                        crate::leanh::lean_dec_ref(v_arg_5121_);
                                                                                        crate::leanh::lean_dec_ref(v_arg_5088_);
                                                                                        crate::leanh::lean_dec_ref(v_arg_5085_);
                                                                                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                                                                                        state = 4;
                                                                                        continue;
                                                                                    } else {
                                                                                        v_arg_5124_ = crate::leanh::lean_ctor_get(v___x_5122_, 1);
                                                                                        crate::leanh::lean_inc_ref(v_arg_5124_);
                                                                                        v___x_5125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5122_);
                                                                                        v___x_5126_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20;
                                                                                        v___x_5127_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5126_);
                                                                                        if v___x_5127_ == 0 {
v___x_5128_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23;
v___x_5129_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5128_);
if v___x_5129_ == 0 {
v___x_5130_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26;
v___x_5131_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5130_);
if v___x_5131_ == 0 {
crate::leanh::lean_dec_ref(v_arg_5124_);
crate::leanh::lean_dec_ref(v_arg_5121_);
v___x_5132_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29;
v___x_5133_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5132_);
if v___x_5133_ == 0 {
v___x_5134_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32;
v___x_5135_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5134_);
if v___x_5135_ == 0 {
v___x_5136_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35;
v___x_5137_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5136_);
if v___x_5137_ == 0 {
v___x_5138_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38;
v___x_5139_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5138_);
if v___x_5139_ == 0 {
v___x_5140_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41;
v___x_5141_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5140_);
if v___x_5141_ == 0 {
v___x_5142_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44;
v___x_5143_ = l_Lean_Expr_isConstOf(v___x_5125_, v___x_5142_);
crate::leanh::lean_dec_ref(v___x_5125_);
if v___x_5143_ == 0 {
crate::leanh::lean_dec_ref(v_arg_5088_);
crate::leanh::lean_dec_ref(v_arg_5085_);
crate::leanh::lean_dec_ref(v_origExpr_5057_);
state = 4; continue;
} else {
crate::leanh::lean_del_object(v___x_5076_);
v___x_5144_ = 0;
v___x_5145_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46;
v___x_5146_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5144_, v___x_5145_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5146_;
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_del_object(v___x_5076_);
v___x_5147_ = 2;
v___x_5148_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48;
v___x_5149_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5147_, v___x_5148_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5149_;
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_del_object(v___x_5076_);
v___x_5150_ = 3;
v___x_5151_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50;
v___x_5152_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5150_, v___x_5151_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5152_;
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_del_object(v___x_5076_);
v___x_5153_ = 4;
v___x_5154_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52;
v___x_5155_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5153_, v___x_5154_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5155_;
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_del_object(v___x_5076_);
v___x_5156_ = 5;
v___x_5157_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54;
v___x_5158_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5156_, v___x_5157_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5158_;
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_del_object(v___x_5076_);
v___x_5159_ = 6;
v___x_5160_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56;
v___x_5161_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5159_, v___x_5160_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5161_;
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_del_object(v___x_5076_);
crate::leanh::lean_inc_ref(v_arg_5085_);
crate::leanh::lean_inc_ref(v_arg_5121_);
v___x_5162_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_5121_, v_arg_5085_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if crate::leanh::lean_obj_tag(v___x_5162_) == 0 {
v_a_5163_ = crate::leanh::lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5216_ = (!crate::leanh::lean_is_exclusive(v___x_5162_)) as u8;
if v_isSharedCheck_5216_ == 0 {
v___x_5165_ = v___x_5162_;
v_isShared_5166_ = v_isSharedCheck_5216_;
state = 6; continue;
} else {
crate::leanh::lean_inc(v_a_5163_);
crate::leanh::lean_dec(v___x_5162_);
v___x_5165_ = crate::leanh::lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5216_;
state = 6; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_5124_);
crate::leanh::lean_dec_ref(v_arg_5121_);
crate::leanh::lean_dec_ref(v_arg_5088_);
crate::leanh::lean_dec_ref(v_arg_5085_);
crate::leanh::lean_dec_ref(v_origExpr_5057_);
v_a_5217_ = crate::leanh::lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5224_ = (!crate::leanh::lean_is_exclusive(v___x_5162_)) as u8;
if v_isSharedCheck_5224_ == 0 {
v___x_5219_ = v___x_5162_;
v_isShared_5220_ = v_isSharedCheck_5224_;
state = 16; continue;
} else {
crate::leanh::lean_inc(v_a_5217_);
crate::leanh::lean_dec(v___x_5162_);
v___x_5219_ = crate::leanh::lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
state = 16; continue;
}
}
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_del_object(v___x_5076_);
crate::leanh::lean_inc_ref(v_arg_5085_);
crate::leanh::lean_inc_ref(v_arg_5121_);
v___x_5225_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_5121_, v_arg_5085_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if crate::leanh::lean_obj_tag(v___x_5225_) == 0 {
v_a_5226_ = crate::leanh::lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5279_ = (!crate::leanh::lean_is_exclusive(v___x_5225_)) as u8;
if v_isSharedCheck_5279_ == 0 {
v___x_5228_ = v___x_5225_;
v_isShared_5229_ = v_isSharedCheck_5279_;
state = 18; continue;
} else {
crate::leanh::lean_inc(v_a_5226_);
crate::leanh::lean_dec(v___x_5225_);
v___x_5228_ = crate::leanh::lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5279_;
state = 18; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_5124_);
crate::leanh::lean_dec_ref(v_arg_5121_);
crate::leanh::lean_dec_ref(v_arg_5088_);
crate::leanh::lean_dec_ref(v_arg_5085_);
crate::leanh::lean_dec_ref(v_origExpr_5057_);
v_a_5280_ = crate::leanh::lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5287_ = (!crate::leanh::lean_is_exclusive(v___x_5225_)) as u8;
if v_isSharedCheck_5287_ == 0 {
v___x_5282_ = v___x_5225_;
v_isShared_5283_ = v_isSharedCheck_5287_;
state = 28; continue;
} else {
crate::leanh::lean_inc(v_a_5280_);
crate::leanh::lean_dec(v___x_5225_);
v___x_5282_ = crate::leanh::lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
state = 28; continue;
}
}
}
} else {
crate::leanh::lean_dec_ref(v___x_5125_);
crate::leanh::lean_dec_ref(v_arg_5124_);
crate::leanh::lean_dec_ref(v_arg_5121_);
crate::leanh::lean_del_object(v___x_5076_);
crate::leanh::lean_inc_ref(v_arg_5088_);
v___x_5288_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5088_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if crate::leanh::lean_obj_tag(v___x_5288_) == 0 {
v_a_5289_ = crate::leanh::lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5352_ = (!crate::leanh::lean_is_exclusive(v___x_5288_)) as u8;
if v_isSharedCheck_5352_ == 0 {
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5352_;
state = 30; continue;
} else {
crate::leanh::lean_inc(v_a_5289_);
crate::leanh::lean_dec(v___x_5288_);
v___x_5291_ = crate::leanh::lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5352_;
state = 30; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_5088_);
crate::leanh::lean_dec_ref(v_arg_5085_);
crate::leanh::lean_dec_ref(v_origExpr_5057_);
return v___x_5288_;
}
}
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                crate::leanh::lean_dec_ref(v___x_5113_);
                                                                                crate::leanh::lean_del_object(v___x_5076_);
                                                                                v___f_5353_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72;
                                                                                v___x_5354_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74;
                                                                                v___x_5355_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76;
                                                                                v___x_5356_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_5085_, v_arg_5088_, v___f_5353_, v___x_5354_, v___x_5355_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                                return v___x_5356_;
                                                                            }
                                                                        } else {
                                                                            crate::leanh::lean_dec_ref(v___x_5113_);
                                                                            crate::leanh::lean_del_object(v___x_5076_);
                                                                            v___x_5357_ = l_Lean_Meta_getNatValue_x3f(v_arg_5100_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                            if crate::leanh::lean_obj_tag(v___x_5357_) == 0 {
v_a_5358_ = crate::leanh::lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5420_ = (!crate::leanh::lean_is_exclusive(v___x_5357_)) as u8;
if v_isSharedCheck_5420_ == 0 {
v___x_5360_ = v___x_5357_;
v_isShared_5361_ = v_isSharedCheck_5420_;
state = 40; continue;
} else {
crate::leanh::lean_inc(v_a_5358_);
crate::leanh::lean_dec(v___x_5357_);
v___x_5360_ = crate::leanh::lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5420_;
state = 40; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_5100_);
crate::leanh::lean_dec_ref(v_arg_5088_);
crate::leanh::lean_dec_ref(v_arg_5085_);
crate::leanh::lean_dec_ref(v_origExpr_5057_);
v_a_5421_ = crate::leanh::lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5428_ = (!crate::leanh::lean_is_exclusive(v___x_5357_)) as u8;
if v_isSharedCheck_5428_ == 0 {
v___x_5423_ = v___x_5357_;
v_isShared_5424_ = v_isSharedCheck_5428_;
state = 51; continue;
} else {
crate::leanh::lean_inc(v_a_5421_);
crate::leanh::lean_dec(v___x_5357_);
v___x_5423_ = crate::leanh::lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
state = 51; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___x_5113_,
                                                                        );
                                                                        crate::leanh::lean_del_object(v___x_5076_);
                                                                        crate::leanh::lean_inc_ref(
                                                                            v_origExpr_5057_,
                                                                        );
                                                                        v___x_5429_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_origExpr_5057_, v___x_5115_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                        if crate::leanh::lean_obj_tag(v___x_5429_) == 0 {
v_a_5430_ = crate::leanh::lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5497_ = (!crate::leanh::lean_is_exclusive(v___x_5429_)) as u8;
if v_isSharedCheck_5497_ == 0 {
v___x_5432_ = v___x_5429_;
v_isShared_5433_ = v_isSharedCheck_5497_;
state = 53; continue;
} else {
crate::leanh::lean_inc(v_a_5430_);
crate::leanh::lean_dec(v___x_5429_);
v___x_5432_ = crate::leanh::lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5497_;
state = 53; continue;
}
} else {
crate::leanh::lean_dec_ref(v_arg_5100_);
crate::leanh::lean_dec_ref(v_arg_5088_);
crate::leanh::lean_dec_ref(v_arg_5085_);
crate::leanh::lean_dec_ref(v_origExpr_5057_);
return v___x_5429_;
}
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_5101_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_5100_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_5088_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_5076_,
                                                                );
                                                                v___x_5498_ =
                                                                    crate::leanh::lean_box(0);
                                                                v___x_5499_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81;
                                                                v___x_5500_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5498_, v___x_5499_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                return v___x_5500_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_5101_);
                                                            crate::leanh::lean_dec_ref(v_arg_5100_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_5076_,
                                                            );
                                                            v___x_5501_ =
                                                                l_Lean_Meta_getNatValue_x3f(
                                                                    v_arg_5085_,
                                                                    v_a_5060_,
                                                                    v_a_5061_,
                                                                    v_a_5062_,
                                                                    v_a_5063_,
                                                                );
                                                            crate::leanh::lean_dec_ref(v_arg_5085_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_5501_,
                                                            ) == 0
                                                            {
                                                                v_a_5502_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_5501_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5515_ = (!crate::leanh::lean_is_exclusive(v___x_5501_)) as u8;
                                                                if v_isSharedCheck_5515_ == 0 {
                                                                    v___x_5504_ = v___x_5501_;
                                                                    v_isShared_5505_ =
                                                                        v_isSharedCheck_5515_;
                                                                    state = 67;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_5502_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_5501_,
                                                                    );
                                                                    v___x_5504_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_5505_ =
                                                                        v_isSharedCheck_5515_;
                                                                    state = 67;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_5088_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_origExpr_5057_,
                                                                );
                                                                v_a_5516_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_5501_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5523_ = (!crate::leanh::lean_is_exclusive(v___x_5501_)) as u8;
                                                                if v_isSharedCheck_5523_ == 0 {
                                                                    v___x_5518_ = v___x_5501_;
                                                                    v_isShared_5519_ =
                                                                        v_isSharedCheck_5523_;
                                                                    state = 69;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_5516_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_5501_,
                                                                    );
                                                                    v___x_5518_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_5519_ =
                                                                        v_isSharedCheck_5523_;
                                                                    state = 69;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_5101_);
                                                        crate::leanh::lean_dec_ref(v_arg_5100_);
                                                        crate::leanh::lean_del_object(v___x_5076_);
                                                        crate::leanh::lean_inc_ref(v_arg_5085_);
                                                        v___x_5524_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                        if crate::leanh::lean_obj_tag(v___x_5524_)
                                                            == 0
                                                        {
                                                            v_a_5525_ = crate::leanh::lean_ctor_get(
                                                                v___x_5524_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5593_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_5524_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5593_ == 0 {
                                                                v___x_5527_ = v___x_5524_;
                                                                v_isShared_5528_ =
                                                                    v_isSharedCheck_5593_;
                                                                state = 71;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_5525_);
                                                                crate::leanh::lean_dec(v___x_5524_);
                                                                v___x_5527_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_5528_ =
                                                                    v_isSharedCheck_5593_;
                                                                state = 71;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_5088_);
                                                            crate::leanh::lean_dec_ref(v_arg_5085_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_origExpr_5057_,
                                                            );
                                                            return v___x_5524_;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_5101_);
                                                    crate::leanh::lean_dec_ref(v_arg_5100_);
                                                    crate::leanh::lean_del_object(v___x_5076_);
                                                    v___f_5594_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87;
                                                    v___x_5595_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5;
                                                    v___x_5596_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89;
                                                    v___x_5597_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_5085_, v_arg_5088_, v___f_5594_, v___x_5595_, v___x_5596_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                    crate::leanh::lean_dec_ref(v_arg_5085_);
                                                    return v___x_5597_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_5101_);
                                                crate::leanh::lean_dec_ref(v_arg_5100_);
                                                crate::leanh::lean_del_object(v___x_5076_);
                                                v___f_5598_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90;
                                                v___x_5599_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8;
                                                v___x_5600_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92;
                                                v___x_5601_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_5085_, v_arg_5088_, v___f_5598_, v___x_5599_, v___x_5600_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                crate::leanh::lean_dec_ref(v_arg_5085_);
                                                return v___x_5601_;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_5089_);
                                        crate::leanh::lean_dec_ref(v_arg_5088_);
                                        crate::leanh::lean_dec_ref(v_arg_5085_);
                                        crate::leanh::lean_del_object(v___x_5076_);
                                        v___x_5602_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_origExpr_5057_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                        return v___x_5602_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5089_);
                                    crate::leanh::lean_dec_ref(v_arg_5088_);
                                    crate::leanh::lean_del_object(v___x_5076_);
                                    v___x_5603_ = crate::leanh::lean_box(4);
                                    v___x_5604_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94;
                                    v___x_5605_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5603_, v___x_5604_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                    return v___x_5605_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5089_);
                                crate::leanh::lean_dec_ref(v_arg_5088_);
                                crate::leanh::lean_del_object(v___x_5076_);
                                v___x_5606_ = crate::leanh::lean_box(5);
                                v___x_5607_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96;
                                v___x_5608_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5606_, v___x_5607_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                return v___x_5608_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5089_);
                            crate::leanh::lean_dec_ref(v_arg_5088_);
                            crate::leanh::lean_del_object(v___x_5076_);
                            v___x_5609_ = crate::leanh::lean_box(6);
                            v___x_5610_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98;
                            v___x_5611_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5609_, v___x_5610_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                            return v___x_5611_;
                        }
                    }
                }
            }
            4 => {
                v___x_5079_ = crate::leanh::lean_box(0);
                if v_isShared_5077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5076_, 0, v___x_5079_);
                    v___x_5081_ = v___x_5076_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5079_);
                    v___x_5081_ = v_reuseFailAlloc_5082_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5081_;
            }
            6 => {
                v___x_5172_ = l_Lean_Expr_cleanupAnnotations(v_arg_5124_);
                v___x_5173_ = l_Lean_Expr_isApp(v___x_5172_);
                if v___x_5173_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5172_);
                    crate::leanh::lean_dec(v_a_5163_);
                    crate::leanh::lean_dec_ref(v_arg_5121_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 7;
                    continue;
                } else {
                    v_arg_5174_ = crate::leanh::lean_ctor_get(v___x_5172_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5174_);
                    v___x_5175_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5172_);
                    v___x_5176_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                    v___x_5177_ = l_Lean_Expr_isConstOf(v___x_5175_, v___x_5176_);
                    crate::leanh::lean_dec_ref(v___x_5175_);
                    if v___x_5177_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_5174_);
                        crate::leanh::lean_dec(v_a_5163_);
                        crate::leanh::lean_dec_ref(v_arg_5121_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5165_);
                        v___x_5178_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_5174_,
                            v_a_5060_,
                            v_a_5061_,
                            v_a_5062_,
                            v_a_5063_,
                        );
                        crate::leanh::lean_dec_ref(v_arg_5174_);
                        if crate::leanh::lean_obj_tag(v___x_5178_) == 0 {
                            v_a_5179_ = crate::leanh::lean_ctor_get(v___x_5178_, 0);
                            crate::leanh::lean_inc(v_a_5179_);
                            crate::leanh::lean_dec_ref_known(v___x_5178_, 1);
                            v___f_5180_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57;
                            if crate::leanh::lean_obj_tag(v_a_5179_) == 0 {
                                v___y_5207_ = v___x_5129_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_a_5179_, 1);
                                v___y_5207_ = v___x_5177_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5163_);
                            crate::leanh::lean_dec_ref(v_arg_5121_);
                            crate::leanh::lean_dec_ref(v_arg_5088_);
                            crate::leanh::lean_dec_ref(v_arg_5085_);
                            crate::leanh::lean_dec_ref(v_origExpr_5057_);
                            v_a_5208_ = crate::leanh::lean_ctor_get(v___x_5178_, 0);
                            v_isSharedCheck_5215_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5178_)) as u8;
                            if v_isSharedCheck_5215_ == 0 {
                                v___x_5210_ = v___x_5178_;
                                v_isShared_5211_ = v_isSharedCheck_5215_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5208_);
                                crate::leanh::lean_dec(v___x_5178_);
                                v___x_5210_ = crate::leanh::lean_box(0);
                                v_isShared_5211_ = v_isSharedCheck_5215_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                v___x_5168_ = crate::leanh::lean_box(0);
                if v_isShared_5166_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5165_, 0, v___x_5168_);
                    v___x_5170_ = v___x_5165_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5168_);
                    v___x_5170_ = v_reuseFailAlloc_5171_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5170_;
            }
            9 => {
                v___x_5188_ = l_Lean_Expr_cleanupAnnotations(v_arg_5121_);
                v___x_5189_ = l_Lean_Expr_isApp(v___x_5188_);
                if v___x_5189_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5188_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 1;
                    continue;
                } else {
                    v___x_5190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5188_);
                    v___x_5191_ = l_Lean_Expr_isConstOf(v___x_5190_, v___x_5176_);
                    crate::leanh::lean_dec_ref(v___x_5190_);
                    if v___x_5191_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5192_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59;
                        v___x_5193_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61;
                        v___x_5194_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_5085_, v_arg_5088_, v___f_5180_, v___x_5192_, v___x_5193_, v_origExpr_5057_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
                        return v___x_5194_;
                    }
                }
            }
            10 => {
                v___x_5196_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63);
                v___x_5197_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v___x_5196_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if crate::leanh::lean_obj_tag(v___x_5197_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5197_, 1);
                    v___y_5182_ = v_a_5058_;
                    v___y_5183_ = v_a_5059_;
                    v___y_5184_ = v_a_5060_;
                    v___y_5185_ = v_a_5061_;
                    v___y_5186_ = v_a_5062_;
                    v___y_5187_ = v_a_5063_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_arg_5121_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5198_ = crate::leanh::lean_ctor_get(v___x_5197_, 0);
                    v_isSharedCheck_5205_ = (!crate::leanh::lean_is_exclusive(v___x_5197_)) as u8;
                    if v_isSharedCheck_5205_ == 0 {
                        v___x_5200_ = v___x_5197_;
                        v_isShared_5201_ = v_isSharedCheck_5205_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5198_);
                        crate::leanh::lean_dec(v___x_5197_);
                        v___x_5200_ = crate::leanh::lean_box(0);
                        v_isShared_5201_ = v_isSharedCheck_5205_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_5201_ == 0 {
                    v___x_5203_ = v___x_5200_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
                    v___x_5203_ = v_reuseFailAlloc_5204_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5203_;
            }
            13 => {
                if v___y_5207_ == 0 {
                    crate::leanh::lean_dec(v_a_5163_);
                    v___y_5182_ = v_a_5058_;
                    v___y_5183_ = v_a_5059_;
                    v___y_5184_ = v_a_5060_;
                    v___y_5185_ = v_a_5061_;
                    v___y_5186_ = v_a_5062_;
                    v___y_5187_ = v_a_5063_;
                    state = 9;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_5163_) == 0 {
                        if v___x_5129_ == 0 {
                            v___y_5182_ = v_a_5058_;
                            v___y_5183_ = v_a_5059_;
                            v___y_5184_ = v_a_5060_;
                            v___y_5185_ = v_a_5061_;
                            v___y_5186_ = v_a_5062_;
                            v___y_5187_ = v_a_5063_;
                            state = 9;
                            continue;
                        } else {
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_5163_, 1);
                        state = 10;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_5211_ == 0 {
                    v___x_5213_ = v___x_5210_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
                    v___x_5213_ = v_reuseFailAlloc_5214_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5213_;
            }
            16 => {
                if v_isShared_5220_ == 0 {
                    v___x_5222_ = v___x_5219_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
                    v___x_5222_ = v_reuseFailAlloc_5223_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5222_;
            }
            18 => {
                v___x_5235_ = l_Lean_Expr_cleanupAnnotations(v_arg_5124_);
                v___x_5236_ = l_Lean_Expr_isApp(v___x_5235_);
                if v___x_5236_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5235_);
                    crate::leanh::lean_dec(v_a_5226_);
                    crate::leanh::lean_dec_ref(v_arg_5121_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 19;
                    continue;
                } else {
                    v_arg_5237_ = crate::leanh::lean_ctor_get(v___x_5235_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5237_);
                    v___x_5238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5235_);
                    v___x_5239_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                    v___x_5240_ = l_Lean_Expr_isConstOf(v___x_5238_, v___x_5239_);
                    crate::leanh::lean_dec_ref(v___x_5238_);
                    if v___x_5240_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_5237_);
                        crate::leanh::lean_dec(v_a_5226_);
                        crate::leanh::lean_dec_ref(v_arg_5121_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_5228_);
                        v___x_5241_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_5237_,
                            v_a_5060_,
                            v_a_5061_,
                            v_a_5062_,
                            v_a_5063_,
                        );
                        crate::leanh::lean_dec_ref(v_arg_5237_);
                        if crate::leanh::lean_obj_tag(v___x_5241_) == 0 {
                            v_a_5242_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
                            crate::leanh::lean_inc(v_a_5242_);
                            crate::leanh::lean_dec_ref_known(v___x_5241_, 1);
                            v___f_5243_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64;
                            if crate::leanh::lean_obj_tag(v_a_5242_) == 0 {
                                v___y_5270_ = v___x_5127_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_a_5242_, 1);
                                v___y_5270_ = v___x_5240_;
                                state = 25;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5226_);
                            crate::leanh::lean_dec_ref(v_arg_5121_);
                            crate::leanh::lean_dec_ref(v_arg_5088_);
                            crate::leanh::lean_dec_ref(v_arg_5085_);
                            crate::leanh::lean_dec_ref(v_origExpr_5057_);
                            v_a_5271_ = crate::leanh::lean_ctor_get(v___x_5241_, 0);
                            v_isSharedCheck_5278_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5241_)) as u8;
                            if v_isSharedCheck_5278_ == 0 {
                                v___x_5273_ = v___x_5241_;
                                v_isShared_5274_ = v_isSharedCheck_5278_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5271_);
                                crate::leanh::lean_dec(v___x_5241_);
                                v___x_5273_ = crate::leanh::lean_box(0);
                                v_isShared_5274_ = v_isSharedCheck_5278_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                }
            }
            19 => {
                v___x_5231_ = crate::leanh::lean_box(0);
                if v_isShared_5229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5228_, 0, v___x_5231_);
                    v___x_5233_ = v___x_5228_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
                    v___x_5233_ = v_reuseFailAlloc_5234_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5233_;
            }
            21 => {
                v___x_5251_ = l_Lean_Expr_cleanupAnnotations(v_arg_5121_);
                v___x_5252_ = l_Lean_Expr_isApp(v___x_5251_);
                if v___x_5252_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5251_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 2;
                    continue;
                } else {
                    v___x_5253_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5251_);
                    v___x_5254_ = l_Lean_Expr_isConstOf(v___x_5253_, v___x_5239_);
                    crate::leanh::lean_dec_ref(v___x_5253_);
                    if v___x_5254_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 2;
                        continue;
                    } else {
                        v___x_5255_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66;
                        v___x_5256_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68;
                        v___x_5257_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_5085_, v_arg_5088_, v___f_5243_, v___x_5255_, v___x_5256_, v_origExpr_5057_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_, v___y_5250_);
                        return v___x_5257_;
                    }
                }
            }
            22 => {
                v___x_5259_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63);
                v___x_5260_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v___x_5259_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if crate::leanh::lean_obj_tag(v___x_5260_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5260_, 1);
                    v___y_5245_ = v_a_5058_;
                    v___y_5246_ = v_a_5059_;
                    v___y_5247_ = v_a_5060_;
                    v___y_5248_ = v_a_5061_;
                    v___y_5249_ = v_a_5062_;
                    v___y_5250_ = v_a_5063_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_arg_5121_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5261_ = crate::leanh::lean_ctor_get(v___x_5260_, 0);
                    v_isSharedCheck_5268_ = (!crate::leanh::lean_is_exclusive(v___x_5260_)) as u8;
                    if v_isSharedCheck_5268_ == 0 {
                        v___x_5263_ = v___x_5260_;
                        v_isShared_5264_ = v_isSharedCheck_5268_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5261_);
                        crate::leanh::lean_dec(v___x_5260_);
                        v___x_5263_ = crate::leanh::lean_box(0);
                        v_isShared_5264_ = v_isSharedCheck_5268_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_5264_ == 0 {
                    v___x_5266_ = v___x_5263_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
                    v___x_5266_ = v_reuseFailAlloc_5267_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5266_;
            }
            25 => {
                if v___y_5270_ == 0 {
                    crate::leanh::lean_dec(v_a_5226_);
                    v___y_5245_ = v_a_5058_;
                    v___y_5246_ = v_a_5059_;
                    v___y_5247_ = v_a_5060_;
                    v___y_5248_ = v_a_5061_;
                    v___y_5249_ = v_a_5062_;
                    v___y_5250_ = v_a_5063_;
                    state = 21;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_5226_) == 0 {
                        if v___x_5127_ == 0 {
                            v___y_5245_ = v_a_5058_;
                            v___y_5246_ = v_a_5059_;
                            v___y_5247_ = v_a_5060_;
                            v___y_5248_ = v_a_5061_;
                            v___y_5249_ = v_a_5062_;
                            v___y_5250_ = v_a_5063_;
                            state = 21;
                            continue;
                        } else {
                            state = 22;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_5226_, 1);
                        state = 22;
                        continue;
                    }
                }
            }
            26 => {
                if v_isShared_5274_ == 0 {
                    v___x_5276_ = v___x_5273_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
                    v___x_5276_ = v_reuseFailAlloc_5277_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_5276_;
            }
            28 => {
                if v_isShared_5283_ == 0 {
                    v___x_5285_ = v___x_5282_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5286_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
                    v___x_5285_ = v_reuseFailAlloc_5286_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5285_;
            }
            30 => {
                if crate::leanh::lean_obj_tag(v_a_5289_) == 1 {
                    crate::leanh::lean_del_object(v___x_5291_);
                    v_val_5293_ = crate::leanh::lean_ctor_get(v_a_5289_, 0);
                    crate::leanh::lean_inc(v_val_5293_);
                    crate::leanh::lean_dec_ref_known(v_a_5289_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5294_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if crate::leanh::lean_obj_tag(v___x_5294_) == 0 {
                        v_a_5295_ = crate::leanh::lean_ctor_get(v___x_5294_, 0);
                        v_isSharedCheck_5347_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5294_)) as u8;
                        if v_isSharedCheck_5347_ == 0 {
                            v___x_5297_ = v___x_5294_;
                            v_isShared_5298_ = v_isSharedCheck_5347_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5295_);
                            crate::leanh::lean_dec(v___x_5294_);
                            v___x_5297_ = crate::leanh::lean_box(0);
                            v_isShared_5298_ = v_isSharedCheck_5347_;
                            state = 31;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5293_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5294_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5289_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5348_ = crate::leanh::lean_box(0);
                    if v_isShared_5292_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5291_, 0, v___x_5348_);
                        v___x_5350_ = v___x_5291_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_5351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
                        v___x_5350_ = v_reuseFailAlloc_5351_;
                        state = 39;
                        continue;
                    }
                }
            }
            31 => {
                if crate::leanh::lean_obj_tag(v_a_5295_) == 1 {
                    crate::leanh::lean_del_object(v___x_5297_);
                    v_val_5299_ = crate::leanh::lean_ctor_get(v_a_5295_, 0);
                    v_isSharedCheck_5342_ = (!crate::leanh::lean_is_exclusive(v_a_5295_)) as u8;
                    if v_isSharedCheck_5342_ == 0 {
                        v___x_5301_ = v_a_5295_;
                        v_isShared_5302_ = v_isSharedCheck_5342_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5299_);
                        crate::leanh::lean_dec(v_a_5295_);
                        v___x_5301_ = crate::leanh::lean_box(0);
                        v_isShared_5302_ = v_isSharedCheck_5342_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5295_);
                    crate::leanh::lean_dec(v_val_5293_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5343_ = crate::leanh::lean_box(0);
                    if v_isShared_5298_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5297_, 0, v___x_5343_);
                        v___x_5345_ = v___x_5297_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_5346_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5343_);
                        v___x_5345_ = v_reuseFailAlloc_5346_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v_width_5303_ = crate::leanh::lean_ctor_get(v_val_5293_, 0);
                crate::leanh::lean_inc_n(v_width_5303_, 2);
                v_bvExpr_5304_ = crate::leanh::lean_ctor_get(v_val_5293_, 1);
                v_expr_5305_ = crate::leanh::lean_ctor_get(v_val_5293_, 4);
                crate::leanh::lean_inc_ref(v_expr_5305_);
                v_width_5306_ = crate::leanh::lean_ctor_get(v_val_5299_, 0);
                crate::leanh::lean_inc_n(v_width_5306_, 2);
                v_bvExpr_5307_ = crate::leanh::lean_ctor_get(v_val_5299_, 1);
                v_expr_5308_ = crate::leanh::lean_ctor_get(v_val_5299_, 4);
                crate::leanh::lean_inc_ref(v_expr_5308_);
                v___x_5309_ = lean_nat_add(v_width_5303_, v_width_5306_);
                crate::leanh::lean_inc_ref(v_bvExpr_5307_);
                crate::leanh::lean_inc_ref(v_bvExpr_5304_);
                crate::leanh::lean_inc_n(v___x_5309_, 2);
                v___x_5310_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(
                    v_width_5303_,
                    v_width_5306_,
                    v___x_5309_,
                    v_bvExpr_5304_,
                    v_bvExpr_5307_,
                );
                v___x_5311_ = l_Lean_mkNatLit(v___x_5309_);
                crate::leanh::lean_inc_ref(v___x_5311_);
                v___x_5312_ =
                    l_Lean_Meta_mkEqRefl(v___x_5311_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if crate::leanh::lean_obj_tag(v___x_5312_) == 0 {
                    v_a_5313_ = crate::leanh::lean_ctor_get(v___x_5312_, 0);
                    v_isSharedCheck_5333_ = (!crate::leanh::lean_is_exclusive(v___x_5312_)) as u8;
                    if v_isSharedCheck_5333_ == 0 {
                        v___x_5315_ = v___x_5312_;
                        v_isShared_5316_ = v_isSharedCheck_5333_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5313_);
                        crate::leanh::lean_dec(v___x_5312_);
                        v___x_5315_ = crate::leanh::lean_box(0);
                        v_isShared_5316_ = v_isSharedCheck_5333_;
                        state = 33;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5311_);
                    crate::leanh::lean_dec_ref(v___x_5310_);
                    crate::leanh::lean_dec(v___x_5309_);
                    crate::leanh::lean_dec_ref(v_expr_5308_);
                    crate::leanh::lean_dec(v_width_5306_);
                    crate::leanh::lean_dec_ref(v_expr_5305_);
                    crate::leanh::lean_dec(v_width_5303_);
                    crate::leanh::lean_del_object(v___x_5301_);
                    crate::leanh::lean_dec(v_val_5299_);
                    crate::leanh::lean_dec(v_val_5293_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5334_ = crate::leanh::lean_ctor_get(v___x_5312_, 0);
                    v_isSharedCheck_5341_ = (!crate::leanh::lean_is_exclusive(v___x_5312_)) as u8;
                    if v_isSharedCheck_5341_ == 0 {
                        v___x_5336_ = v___x_5312_;
                        v_isShared_5337_ = v_isSharedCheck_5341_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5334_);
                        crate::leanh::lean_dec(v___x_5312_);
                        v___x_5336_ = crate::leanh::lean_box(0);
                        v_isShared_5337_ = v_isSharedCheck_5341_;
                        state = 36;
                        continue;
                    }
                }
            }
            33 => {
                v___x_5317_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0;
                v___x_5318_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1;
                v___x_5319_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2;
                v___x_5320_ = crate::leanh::lean_box(0);
                v___x_5321_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71);
                crate::leanh::lean_inc(v_width_5303_);
                v___x_5322_ = l_Lean_mkNatLit(v_width_5303_);
                crate::leanh::lean_inc(v_width_5306_);
                v___x_5323_ = l_Lean_mkNatLit(v_width_5306_);
                crate::leanh::lean_inc_ref(v___x_5323_);
                crate::leanh::lean_inc_ref(v___x_5322_);
                crate::leanh::lean_inc_ref(v_expr_5308_);
                crate::leanh::lean_inc_ref(v_expr_5305_);
                v___f_5324_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___boxed as *mut core::ffi::c_void, 21, 15);
                crate::leanh::lean_closure_set(v___f_5324_, 0, v_width_5303_);
                crate::leanh::lean_closure_set(v___f_5324_, 1, v_expr_5305_);
                crate::leanh::lean_closure_set(v___f_5324_, 2, v_width_5306_);
                crate::leanh::lean_closure_set(v___f_5324_, 3, v_expr_5308_);
                crate::leanh::lean_closure_set(v___f_5324_, 4, v_val_5293_);
                crate::leanh::lean_closure_set(v___f_5324_, 5, v_val_5299_);
                crate::leanh::lean_closure_set(v___f_5324_, 6, v___x_5317_);
                crate::leanh::lean_closure_set(v___f_5324_, 7, v___x_5318_);
                crate::leanh::lean_closure_set(v___f_5324_, 8, v___x_5319_);
                crate::leanh::lean_closure_set(v___f_5324_, 9, v___x_5090_);
                crate::leanh::lean_closure_set(v___f_5324_, 10, v___x_5320_);
                crate::leanh::lean_closure_set(v___f_5324_, 11, v___x_5322_);
                crate::leanh::lean_closure_set(v___f_5324_, 12, v___x_5323_);
                crate::leanh::lean_closure_set(v___f_5324_, 13, v_arg_5088_);
                crate::leanh::lean_closure_set(v___f_5324_, 14, v_arg_5085_);
                v___x_5325_ = l_Lean_mkApp6(
                    v___x_5321_,
                    v___x_5322_,
                    v___x_5323_,
                    v___x_5311_,
                    v_expr_5305_,
                    v_expr_5308_,
                    v_a_5313_,
                );
                v___x_5326_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5326_, 0, v___x_5309_);
                crate::leanh::lean_ctor_set(v___x_5326_, 1, v___x_5310_);
                crate::leanh::lean_ctor_set(v___x_5326_, 2, v_origExpr_5057_);
                crate::leanh::lean_ctor_set(v___x_5326_, 3, v___f_5324_);
                crate::leanh::lean_ctor_set(v___x_5326_, 4, v___x_5325_);
                if v_isShared_5302_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5301_, 0, v___x_5326_);
                    v___x_5328_ = v___x_5301_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5332_, 0, v___x_5326_);
                    v___x_5328_ = v_reuseFailAlloc_5332_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_5316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5315_, 0, v___x_5328_);
                    v___x_5330_ = v___x_5315_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
                    v___x_5330_ = v_reuseFailAlloc_5331_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5330_;
            }
            36 => {
                if v_isShared_5337_ == 0 {
                    v___x_5339_ = v___x_5336_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
                    v___x_5339_ = v_reuseFailAlloc_5340_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_5339_;
            }
            38 => {
                return v___x_5345_;
            }
            39 => {
                return v___x_5350_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v_a_5358_) == 1 {
                    crate::leanh::lean_del_object(v___x_5360_);
                    v_val_5362_ = crate::leanh::lean_ctor_get(v_a_5358_, 0);
                    crate::leanh::lean_inc(v_val_5362_);
                    crate::leanh::lean_dec_ref_known(v_a_5358_, 1);
                    v___x_5363_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_5088_,
                        v_a_5060_,
                        v_a_5061_,
                        v_a_5062_,
                        v_a_5063_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5363_) == 0 {
                        v_a_5364_ = crate::leanh::lean_ctor_get(v___x_5363_, 0);
                        v_isSharedCheck_5407_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5363_)) as u8;
                        if v_isSharedCheck_5407_ == 0 {
                            v___x_5366_ = v___x_5363_;
                            v_isShared_5367_ = v_isSharedCheck_5407_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5364_);
                            crate::leanh::lean_dec(v___x_5363_);
                            v___x_5366_ = crate::leanh::lean_box(0);
                            v_isShared_5367_ = v_isSharedCheck_5407_;
                            state = 41;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5362_);
                        crate::leanh::lean_dec_ref(v_arg_5100_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5408_ = crate::leanh::lean_ctor_get(v___x_5363_, 0);
                        v_isSharedCheck_5415_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5363_)) as u8;
                        if v_isSharedCheck_5415_ == 0 {
                            v___x_5410_ = v___x_5363_;
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 48;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5408_);
                            crate::leanh::lean_dec(v___x_5363_);
                            v___x_5410_ = crate::leanh::lean_box(0);
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 48;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5358_);
                    crate::leanh::lean_dec_ref(v_arg_5100_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5416_ = crate::leanh::lean_box(0);
                    if v_isShared_5361_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5360_, 0, v___x_5416_);
                        v___x_5418_ = v___x_5360_;
                        state = 50;
                        continue;
                    } else {
                        v_reuseFailAlloc_5419_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5416_);
                        v___x_5418_ = v_reuseFailAlloc_5419_;
                        state = 50;
                        continue;
                    }
                }
            }
            41 => {
                if crate::leanh::lean_obj_tag(v_a_5364_) == 1 {
                    crate::leanh::lean_del_object(v___x_5366_);
                    v_val_5368_ = crate::leanh::lean_ctor_get(v_a_5364_, 0);
                    crate::leanh::lean_inc(v_val_5368_);
                    crate::leanh::lean_dec_ref_known(v_a_5364_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5369_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if crate::leanh::lean_obj_tag(v___x_5369_) == 0 {
                        v_a_5370_ = crate::leanh::lean_ctor_get(v___x_5369_, 0);
                        v_isSharedCheck_5402_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5369_)) as u8;
                        if v_isSharedCheck_5402_ == 0 {
                            v___x_5372_ = v___x_5369_;
                            v_isShared_5373_ = v_isSharedCheck_5402_;
                            state = 42;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5370_);
                            crate::leanh::lean_dec(v___x_5369_);
                            v___x_5372_ = crate::leanh::lean_box(0);
                            v_isShared_5373_ = v_isSharedCheck_5402_;
                            state = 42;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5368_);
                        crate::leanh::lean_dec(v_val_5362_);
                        crate::leanh::lean_dec_ref(v_arg_5100_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5369_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5364_);
                    crate::leanh::lean_dec(v_val_5362_);
                    crate::leanh::lean_dec_ref(v_arg_5100_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5403_ = crate::leanh::lean_box(0);
                    if v_isShared_5367_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5366_, 0, v___x_5403_);
                        v___x_5405_ = v___x_5366_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_5406_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5403_);
                        v___x_5405_ = v_reuseFailAlloc_5406_;
                        state = 47;
                        continue;
                    }
                }
            }
            42 => {
                if crate::leanh::lean_obj_tag(v_a_5370_) == 1 {
                    v_val_5374_ = crate::leanh::lean_ctor_get(v_a_5370_, 0);
                    v_isSharedCheck_5397_ = (!crate::leanh::lean_is_exclusive(v_a_5370_)) as u8;
                    if v_isSharedCheck_5397_ == 0 {
                        v___x_5376_ = v_a_5370_;
                        v_isShared_5377_ = v_isSharedCheck_5397_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5374_);
                        crate::leanh::lean_dec(v_a_5370_);
                        v___x_5376_ = crate::leanh::lean_box(0);
                        v_isShared_5377_ = v_isSharedCheck_5397_;
                        state = 43;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5370_);
                    crate::leanh::lean_dec(v_val_5368_);
                    crate::leanh::lean_dec(v_val_5362_);
                    crate::leanh::lean_dec_ref(v_arg_5100_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5398_ = crate::leanh::lean_box(0);
                    if v_isShared_5373_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5372_, 0, v___x_5398_);
                        v___x_5400_ = v___x_5372_;
                        state = 46;
                        continue;
                    } else {
                        v_reuseFailAlloc_5401_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
                        v___x_5400_ = v_reuseFailAlloc_5401_;
                        state = 46;
                        continue;
                    }
                }
            }
            43 => {
                v_width_5378_ = crate::leanh::lean_ctor_get(v_val_5374_, 0);
                crate::leanh::lean_inc_n(v_width_5378_, 3);
                v_bvExpr_5379_ = crate::leanh::lean_ctor_get(v_val_5374_, 1);
                v_expr_5380_ = crate::leanh::lean_ctor_get(v_val_5374_, 4);
                crate::leanh::lean_inc_ref_n(v_expr_5380_, 2);
                crate::leanh::lean_inc_ref(v_bvExpr_5379_);
                crate::leanh::lean_inc(v_val_5368_);
                v___x_5381_ = l_Std_Tactic_BVDecide_BVExpr_extract___override(
                    v_width_5378_,
                    v_val_5362_,
                    v_val_5368_,
                    v_bvExpr_5379_,
                );
                v___x_5382_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0;
                v___x_5383_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1;
                v___x_5384_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2;
                v___x_5385_ = crate::leanh::lean_box(0);
                v___x_5386_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79);
                v___x_5387_ = l_Lean_mkNatLit(v_width_5378_);
                crate::leanh::lean_inc_ref(v___x_5387_);
                crate::leanh::lean_inc_ref(v_arg_5088_);
                crate::leanh::lean_inc_ref(v_arg_5100_);
                v___f_5388_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___boxed as *mut core::ffi::c_void, 18, 12);
                crate::leanh::lean_closure_set(v___f_5388_, 0, v_width_5378_);
                crate::leanh::lean_closure_set(v___f_5388_, 1, v_expr_5380_);
                crate::leanh::lean_closure_set(v___f_5388_, 2, v_val_5374_);
                crate::leanh::lean_closure_set(v___f_5388_, 3, v___x_5382_);
                crate::leanh::lean_closure_set(v___f_5388_, 4, v___x_5383_);
                crate::leanh::lean_closure_set(v___f_5388_, 5, v___x_5384_);
                crate::leanh::lean_closure_set(v___f_5388_, 6, v___x_5090_);
                crate::leanh::lean_closure_set(v___f_5388_, 7, v___x_5385_);
                crate::leanh::lean_closure_set(v___f_5388_, 8, v_arg_5100_);
                crate::leanh::lean_closure_set(v___f_5388_, 9, v_arg_5088_);
                crate::leanh::lean_closure_set(v___f_5388_, 10, v___x_5387_);
                crate::leanh::lean_closure_set(v___f_5388_, 11, v_arg_5085_);
                v___x_5389_ = l_Lean_mkApp4(
                    v___x_5386_,
                    v___x_5387_,
                    v_arg_5100_,
                    v_arg_5088_,
                    v_expr_5380_,
                );
                v___x_5390_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5390_, 0, v_val_5368_);
                crate::leanh::lean_ctor_set(v___x_5390_, 1, v___x_5381_);
                crate::leanh::lean_ctor_set(v___x_5390_, 2, v_origExpr_5057_);
                crate::leanh::lean_ctor_set(v___x_5390_, 3, v___f_5388_);
                crate::leanh::lean_ctor_set(v___x_5390_, 4, v___x_5389_);
                if v_isShared_5377_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5376_, 0, v___x_5390_);
                    v___x_5392_ = v___x_5376_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5396_, 0, v___x_5390_);
                    v___x_5392_ = v_reuseFailAlloc_5396_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_5373_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5372_, 0, v___x_5392_);
                    v___x_5394_ = v___x_5372_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_5395_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5395_, 0, v___x_5392_);
                    v___x_5394_ = v_reuseFailAlloc_5395_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_5394_;
            }
            46 => {
                return v___x_5400_;
            }
            47 => {
                return v___x_5405_;
            }
            48 => {
                if v_isShared_5411_ == 0 {
                    v___x_5413_ = v___x_5410_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_5414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
                    v___x_5413_ = v_reuseFailAlloc_5414_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_5413_;
            }
            50 => {
                return v___x_5418_;
            }
            51 => {
                if v_isShared_5424_ == 0 {
                    v___x_5426_ = v___x_5423_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
                    v___x_5426_ = v_reuseFailAlloc_5427_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5426_;
            }
            53 => {
                if crate::leanh::lean_obj_tag(v_a_5430_) == 1 {
                    crate::leanh::lean_del_object(v___x_5432_);
                    v_val_5434_ = crate::leanh::lean_ctor_get(v_a_5430_, 0);
                    crate::leanh::lean_inc_ref(v_arg_5100_);
                    v___x_5435_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(
                        v_arg_5100_,
                        v_a_5058_,
                        v_a_5059_,
                        v_a_5060_,
                        v_a_5061_,
                        v_a_5062_,
                        v_a_5063_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5435_) == 0 {
                        v_a_5436_ = crate::leanh::lean_ctor_get(v___x_5435_, 0);
                        v_isSharedCheck_5484_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5435_)) as u8;
                        if v_isSharedCheck_5484_ == 0 {
                            v___x_5438_ = v___x_5435_;
                            v_isShared_5439_ = v_isSharedCheck_5484_;
                            state = 54;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5436_);
                            crate::leanh::lean_dec(v___x_5435_);
                            v___x_5438_ = crate::leanh::lean_box(0);
                            v_isShared_5439_ = v_isSharedCheck_5484_;
                            state = 54;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_5430_, 1);
                        crate::leanh::lean_dec_ref(v_arg_5100_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5485_ = crate::leanh::lean_ctor_get(v___x_5435_, 0);
                        v_isSharedCheck_5492_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5435_)) as u8;
                        if v_isSharedCheck_5492_ == 0 {
                            v___x_5487_ = v___x_5435_;
                            v_isShared_5488_ = v_isSharedCheck_5492_;
                            state = 64;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5485_);
                            crate::leanh::lean_dec(v___x_5435_);
                            v___x_5487_ = crate::leanh::lean_box(0);
                            v_isShared_5488_ = v_isSharedCheck_5492_;
                            state = 64;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5430_);
                    crate::leanh::lean_dec_ref(v_arg_5100_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5493_ = crate::leanh::lean_box(0);
                    if v_isShared_5433_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5432_, 0, v___x_5493_);
                        v___x_5495_ = v___x_5432_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_5496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
                        v___x_5495_ = v_reuseFailAlloc_5496_;
                        state = 66;
                        continue;
                    }
                }
            }
            54 => {
                if crate::leanh::lean_obj_tag(v_a_5436_) == 1 {
                    crate::leanh::lean_del_object(v___x_5438_);
                    v_val_5440_ = crate::leanh::lean_ctor_get(v_a_5436_, 0);
                    crate::leanh::lean_inc(v_val_5440_);
                    crate::leanh::lean_dec_ref_known(v_a_5436_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5088_);
                    v___x_5441_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5088_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if crate::leanh::lean_obj_tag(v___x_5441_) == 0 {
                        v_a_5442_ = crate::leanh::lean_ctor_get(v___x_5441_, 0);
                        v_isSharedCheck_5479_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5441_)) as u8;
                        if v_isSharedCheck_5479_ == 0 {
                            v___x_5444_ = v___x_5441_;
                            v_isShared_5445_ = v_isSharedCheck_5479_;
                            state = 55;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5442_);
                            crate::leanh::lean_dec(v___x_5441_);
                            v___x_5444_ = crate::leanh::lean_box(0);
                            v_isShared_5445_ = v_isSharedCheck_5479_;
                            state = 55;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5440_);
                        crate::leanh::lean_dec_ref_known(v_a_5430_, 1);
                        crate::leanh::lean_dec_ref(v_arg_5100_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5441_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5436_);
                    crate::leanh::lean_dec_ref_known(v_a_5430_, 1);
                    crate::leanh::lean_dec_ref(v_arg_5100_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5480_ = crate::leanh::lean_box(0);
                    if v_isShared_5439_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5438_, 0, v___x_5480_);
                        v___x_5482_ = v___x_5438_;
                        state = 63;
                        continue;
                    } else {
                        v_reuseFailAlloc_5483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5480_);
                        v___x_5482_ = v_reuseFailAlloc_5483_;
                        state = 63;
                        continue;
                    }
                }
            }
            55 => {
                if crate::leanh::lean_obj_tag(v_a_5442_) == 1 {
                    crate::leanh::lean_del_object(v___x_5444_);
                    v_val_5446_ = crate::leanh::lean_ctor_get(v_a_5442_, 0);
                    crate::leanh::lean_inc(v_val_5446_);
                    crate::leanh::lean_dec_ref_known(v_a_5442_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5447_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if crate::leanh::lean_obj_tag(v___x_5447_) == 0 {
                        v_a_5448_ = crate::leanh::lean_ctor_get(v___x_5447_, 0);
                        v_isSharedCheck_5474_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5447_)) as u8;
                        if v_isSharedCheck_5474_ == 0 {
                            v___x_5450_ = v___x_5447_;
                            v_isShared_5451_ = v_isSharedCheck_5474_;
                            state = 56;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5448_);
                            crate::leanh::lean_dec(v___x_5447_);
                            v___x_5450_ = crate::leanh::lean_box(0);
                            v_isShared_5451_ = v_isSharedCheck_5474_;
                            state = 56;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5446_);
                        crate::leanh::lean_dec(v_val_5440_);
                        crate::leanh::lean_dec_ref_known(v_a_5430_, 1);
                        crate::leanh::lean_dec_ref(v_arg_5100_);
                        crate::leanh::lean_dec_ref(v_arg_5088_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5447_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5442_);
                    crate::leanh::lean_dec(v_val_5440_);
                    crate::leanh::lean_dec_ref_known(v_a_5430_, 1);
                    crate::leanh::lean_dec_ref(v_arg_5100_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5475_ = crate::leanh::lean_box(0);
                    if v_isShared_5445_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5444_, 0, v___x_5475_);
                        v___x_5477_ = v___x_5444_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_5478_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5475_);
                        v___x_5477_ = v_reuseFailAlloc_5478_;
                        state = 62;
                        continue;
                    }
                }
            }
            56 => {
                if crate::leanh::lean_obj_tag(v_a_5448_) == 1 {
                    crate::leanh::lean_del_object(v___x_5450_);
                    v_val_5452_ = crate::leanh::lean_ctor_get(v_a_5448_, 0);
                    crate::leanh::lean_inc(v_val_5452_);
                    crate::leanh::lean_dec_ref_known(v_a_5448_, 1);
                    crate::leanh::lean_inc(v_val_5434_);
                    v___x_5453_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(
                        v_val_5440_,
                        v_val_5434_,
                        v_val_5446_,
                        v_val_5452_,
                        v_arg_5100_,
                        v_origExpr_5057_,
                        v_arg_5088_,
                        v_arg_5085_,
                        v_a_5058_,
                        v_a_5060_,
                        v_a_5061_,
                        v_a_5062_,
                        v_a_5063_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5453_) == 0 {
                        v_isSharedCheck_5460_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5453_)) as u8;
                        if v_isSharedCheck_5460_ == 0 {
                            v_unused_5461_ = crate::leanh::lean_ctor_get(v___x_5453_, 0);
                            crate::leanh::lean_dec(v_unused_5461_);
                            v___x_5455_ = v___x_5453_;
                            v_isShared_5456_ = v_isSharedCheck_5460_;
                            state = 57;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5453_);
                            v___x_5455_ = crate::leanh::lean_box(0);
                            v_isShared_5456_ = v_isSharedCheck_5460_;
                            state = 57;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_5430_, 1);
                        v_a_5462_ = crate::leanh::lean_ctor_get(v___x_5453_, 0);
                        v_isSharedCheck_5469_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5453_)) as u8;
                        if v_isSharedCheck_5469_ == 0 {
                            v___x_5464_ = v___x_5453_;
                            v_isShared_5465_ = v_isSharedCheck_5469_;
                            state = 59;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5462_);
                            crate::leanh::lean_dec(v___x_5453_);
                            v___x_5464_ = crate::leanh::lean_box(0);
                            v_isShared_5465_ = v_isSharedCheck_5469_;
                            state = 59;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5448_);
                    crate::leanh::lean_dec(v_val_5446_);
                    crate::leanh::lean_dec(v_val_5440_);
                    crate::leanh::lean_dec_ref_known(v_a_5430_, 1);
                    crate::leanh::lean_dec_ref(v_arg_5100_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5470_ = crate::leanh::lean_box(0);
                    if v_isShared_5451_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5450_, 0, v___x_5470_);
                        v___x_5472_ = v___x_5450_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_5473_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5470_);
                        v___x_5472_ = v_reuseFailAlloc_5473_;
                        state = 61;
                        continue;
                    }
                }
            }
            57 => {
                if v_isShared_5456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5455_, 0, v_a_5430_);
                    v___x_5458_ = v___x_5455_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_5459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5430_);
                    v___x_5458_ = v_reuseFailAlloc_5459_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_5458_;
            }
            59 => {
                if v_isShared_5465_ == 0 {
                    v___x_5467_ = v___x_5464_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_5468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
                    v___x_5467_ = v_reuseFailAlloc_5468_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_5467_;
            }
            61 => {
                return v___x_5472_;
            }
            62 => {
                return v___x_5477_;
            }
            63 => {
                return v___x_5482_;
            }
            64 => {
                if v_isShared_5488_ == 0 {
                    v___x_5490_ = v___x_5487_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
                    v___x_5490_ = v_reuseFailAlloc_5491_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_5490_;
            }
            66 => {
                return v___x_5495_;
            }
            67 => {
                if crate::leanh::lean_obj_tag(v_a_5502_) == 1 {
                    crate::leanh::lean_del_object(v___x_5504_);
                    v_val_5506_ = crate::leanh::lean_ctor_get(v_a_5502_, 0);
                    crate::leanh::lean_inc(v_val_5506_);
                    crate::leanh::lean_dec_ref_known(v_a_5502_, 1);
                    v___f_5507_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82;
                    v___x_5508_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11;
                    v___x_5509_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84;
                    v___x_5510_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_5506_, v_arg_5088_, v___f_5507_, v___x_5508_, v___x_5509_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    return v___x_5510_;
                } else {
                    crate::leanh::lean_dec(v_a_5502_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5511_ = crate::leanh::lean_box(0);
                    if v_isShared_5505_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5504_, 0, v___x_5511_);
                        v___x_5513_ = v___x_5504_;
                        state = 68;
                        continue;
                    } else {
                        v_reuseFailAlloc_5514_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5511_);
                        v___x_5513_ = v_reuseFailAlloc_5514_;
                        state = 68;
                        continue;
                    }
                }
            }
            68 => {
                return v___x_5513_;
            }
            69 => {
                if v_isShared_5519_ == 0 {
                    v___x_5521_ = v___x_5518_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_5522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5516_);
                    v___x_5521_ = v_reuseFailAlloc_5522_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_5521_;
            }
            71 => {
                if crate::leanh::lean_obj_tag(v_a_5525_) == 1 {
                    crate::leanh::lean_del_object(v___x_5527_);
                    v_val_5529_ = crate::leanh::lean_ctor_get(v_a_5525_, 0);
                    crate::leanh::lean_inc(v_val_5529_);
                    crate::leanh::lean_dec_ref_known(v_a_5525_, 1);
                    v___x_5530_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_5088_,
                        v_a_5060_,
                        v_a_5061_,
                        v_a_5062_,
                        v_a_5063_,
                    );
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    if crate::leanh::lean_obj_tag(v___x_5530_) == 0 {
                        v_a_5531_ = crate::leanh::lean_ctor_get(v___x_5530_, 0);
                        v_isSharedCheck_5580_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5530_)) as u8;
                        if v_isSharedCheck_5580_ == 0 {
                            v___x_5533_ = v___x_5530_;
                            v_isShared_5534_ = v_isSharedCheck_5580_;
                            state = 72;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5531_);
                            crate::leanh::lean_dec(v___x_5530_);
                            v___x_5533_ = crate::leanh::lean_box(0);
                            v_isShared_5534_ = v_isSharedCheck_5580_;
                            state = 72;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5529_);
                        crate::leanh::lean_dec_ref(v_arg_5085_);
                        crate::leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5581_ = crate::leanh::lean_ctor_get(v___x_5530_, 0);
                        v_isSharedCheck_5588_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5530_)) as u8;
                        if v_isSharedCheck_5588_ == 0 {
                            v___x_5583_ = v___x_5530_;
                            v_isShared_5584_ = v_isSharedCheck_5588_;
                            state = 80;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5581_);
                            crate::leanh::lean_dec(v___x_5530_);
                            v___x_5583_ = crate::leanh::lean_box(0);
                            v_isShared_5584_ = v_isSharedCheck_5588_;
                            state = 80;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5525_);
                    crate::leanh::lean_dec_ref(v_arg_5088_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5589_ = crate::leanh::lean_box(0);
                    if v_isShared_5528_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5527_, 0, v___x_5589_);
                        v___x_5591_ = v___x_5527_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_5592_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5589_);
                        v___x_5591_ = v_reuseFailAlloc_5592_;
                        state = 82;
                        continue;
                    }
                }
            }
            72 => {
                if crate::leanh::lean_obj_tag(v_a_5531_) == 1 {
                    crate::leanh::lean_del_object(v___x_5533_);
                    v_val_5535_ = crate::leanh::lean_ctor_get(v_a_5531_, 0);
                    v_isSharedCheck_5575_ = (!crate::leanh::lean_is_exclusive(v_a_5531_)) as u8;
                    if v_isSharedCheck_5575_ == 0 {
                        v___x_5537_ = v_a_5531_;
                        v_isShared_5538_ = v_isSharedCheck_5575_;
                        state = 73;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5535_);
                        crate::leanh::lean_dec(v_a_5531_);
                        v___x_5537_ = crate::leanh::lean_box(0);
                        v_isShared_5538_ = v_isSharedCheck_5575_;
                        state = 73;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5531_);
                    crate::leanh::lean_dec(v_val_5529_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5576_ = crate::leanh::lean_box(0);
                    if v_isShared_5534_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5533_, 0, v___x_5576_);
                        v___x_5578_ = v___x_5533_;
                        state = 79;
                        continue;
                    } else {
                        v_reuseFailAlloc_5579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5576_);
                        v___x_5578_ = v_reuseFailAlloc_5579_;
                        state = 79;
                        continue;
                    }
                }
            }
            73 => {
                v_width_5539_ = crate::leanh::lean_ctor_get(v_val_5529_, 0);
                crate::leanh::lean_inc_n(v_width_5539_, 2);
                v_bvExpr_5540_ = crate::leanh::lean_ctor_get(v_val_5529_, 1);
                v_expr_5541_ = crate::leanh::lean_ctor_get(v_val_5529_, 4);
                crate::leanh::lean_inc_ref(v_expr_5541_);
                v___x_5542_ = lean_nat_mul(v_width_5539_, v_val_5535_);
                crate::leanh::lean_inc_ref(v_bvExpr_5540_);
                crate::leanh::lean_inc(v_val_5535_);
                crate::leanh::lean_inc_n(v___x_5542_, 2);
                v___x_5543_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(
                    v_width_5539_,
                    v___x_5542_,
                    v_val_5535_,
                    v_bvExpr_5540_,
                );
                v___x_5544_ = l_Lean_mkNatLit(v___x_5542_);
                crate::leanh::lean_inc_ref(v___x_5544_);
                v___x_5545_ =
                    l_Lean_Meta_mkEqRefl(v___x_5544_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if crate::leanh::lean_obj_tag(v___x_5545_) == 0 {
                    v_a_5546_ = crate::leanh::lean_ctor_get(v___x_5545_, 0);
                    v_isSharedCheck_5566_ = (!crate::leanh::lean_is_exclusive(v___x_5545_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v___x_5548_ = v___x_5545_;
                        v_isShared_5549_ = v_isSharedCheck_5566_;
                        state = 74;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5546_);
                        crate::leanh::lean_dec(v___x_5545_);
                        v___x_5548_ = crate::leanh::lean_box(0);
                        v_isShared_5549_ = v_isSharedCheck_5566_;
                        state = 74;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5544_);
                    crate::leanh::lean_dec_ref(v___x_5543_);
                    crate::leanh::lean_dec(v___x_5542_);
                    crate::leanh::lean_dec_ref(v_expr_5541_);
                    crate::leanh::lean_dec(v_width_5539_);
                    crate::leanh::lean_del_object(v___x_5537_);
                    crate::leanh::lean_dec(v_val_5535_);
                    crate::leanh::lean_dec(v_val_5529_);
                    crate::leanh::lean_dec_ref(v_arg_5085_);
                    crate::leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5567_ = crate::leanh::lean_ctor_get(v___x_5545_, 0);
                    v_isSharedCheck_5574_ = (!crate::leanh::lean_is_exclusive(v___x_5545_)) as u8;
                    if v_isSharedCheck_5574_ == 0 {
                        v___x_5569_ = v___x_5545_;
                        v_isShared_5570_ = v_isSharedCheck_5574_;
                        state = 77;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5567_);
                        crate::leanh::lean_dec(v___x_5545_);
                        v___x_5569_ = crate::leanh::lean_box(0);
                        v_isShared_5570_ = v_isSharedCheck_5574_;
                        state = 77;
                        continue;
                    }
                }
            }
            74 => {
                v___x_5550_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0;
                v___x_5551_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1;
                v___x_5552_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2;
                v___x_5553_ = crate::leanh::lean_box(0);
                v___x_5554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86);
                crate::leanh::lean_inc(v_width_5539_);
                v___x_5555_ = l_Lean_mkNatLit(v_width_5539_);
                v___x_5556_ = l_Lean_mkNatLit(v_val_5535_);
                crate::leanh::lean_inc_ref(v___x_5555_);
                crate::leanh::lean_inc_ref(v___x_5556_);
                crate::leanh::lean_inc_ref(v_expr_5541_);
                v___f_5557_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed as *mut core::ffi::c_void, 17, 11);
                crate::leanh::lean_closure_set(v___f_5557_, 0, v_width_5539_);
                crate::leanh::lean_closure_set(v___f_5557_, 1, v_expr_5541_);
                crate::leanh::lean_closure_set(v___f_5557_, 2, v_val_5529_);
                crate::leanh::lean_closure_set(v___f_5557_, 3, v___x_5550_);
                crate::leanh::lean_closure_set(v___f_5557_, 4, v___x_5551_);
                crate::leanh::lean_closure_set(v___f_5557_, 5, v___x_5552_);
                crate::leanh::lean_closure_set(v___f_5557_, 6, v___x_5090_);
                crate::leanh::lean_closure_set(v___f_5557_, 7, v___x_5553_);
                crate::leanh::lean_closure_set(v___f_5557_, 8, v___x_5556_);
                crate::leanh::lean_closure_set(v___f_5557_, 9, v___x_5555_);
                crate::leanh::lean_closure_set(v___f_5557_, 10, v_arg_5085_);
                v___x_5558_ = l_Lean_mkApp5(
                    v___x_5554_,
                    v___x_5555_,
                    v___x_5544_,
                    v___x_5556_,
                    v_expr_5541_,
                    v_a_5546_,
                );
                v___x_5559_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5559_, 0, v___x_5542_);
                crate::leanh::lean_ctor_set(v___x_5559_, 1, v___x_5543_);
                crate::leanh::lean_ctor_set(v___x_5559_, 2, v_origExpr_5057_);
                crate::leanh::lean_ctor_set(v___x_5559_, 3, v___f_5557_);
                crate::leanh::lean_ctor_set(v___x_5559_, 4, v___x_5558_);
                if v_isShared_5538_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5537_, 0, v___x_5559_);
                    v___x_5561_ = v___x_5537_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5559_);
                    v___x_5561_ = v_reuseFailAlloc_5565_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_5549_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5548_, 0, v___x_5561_);
                    v___x_5563_ = v___x_5548_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_5564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5561_);
                    v___x_5563_ = v_reuseFailAlloc_5564_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                return v___x_5563_;
            }
            77 => {
                if v_isShared_5570_ == 0 {
                    v___x_5572_ = v___x_5569_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_5573_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
                    v___x_5572_ = v_reuseFailAlloc_5573_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                return v___x_5572_;
            }
            79 => {
                return v___x_5578_;
            }
            80 => {
                if v_isShared_5584_ == 0 {
                    v___x_5586_ = v___x_5583_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_5587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
                    v___x_5586_ = v_reuseFailAlloc_5587_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                return v___x_5586_;
            }
            82 => {
                return v___x_5591_;
            }
            83 => {
                if v_isShared_5616_ == 0 {
                    v___x_5618_ = v___x_5615_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_5619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
                    v___x_5618_ = v_reuseFailAlloc_5619_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_5618_;
            }
            85 => {
                if v_isShared_5624_ == 0 {
                    v___x_5626_ = v___x_5623_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_5627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
                    v___x_5626_ = v_reuseFailAlloc_5627_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_5626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(
    mut v_e_5629_: *mut crate::leanh::LeanObject,
    mut v_a_5630_: *mut crate::leanh::LeanObject,
    mut v_a_5631_: *mut crate::leanh::LeanObject,
    mut v_a_5632_: *mut crate::leanh::LeanObject,
    mut v_a_5633_: *mut crate::leanh::LeanObject,
    mut v_a_5634_: *mut crate::leanh::LeanObject,
    mut v_a_5635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5650_: u8 = 0;
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5661_ = lean_st_ref_get(v_a_5630_);
                v_bvExprCache_5662_ = crate::leanh::lean_ctor_get(v___x_5661_, 1);
                crate::leanh::lean_inc_ref(v_bvExprCache_5662_);
                crate::leanh::lean_dec(v___x_5661_);
                v___x_5663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvExprCache_5662_, v_e_5629_);
                crate::leanh::lean_dec_ref(v_bvExprCache_5662_);
                if crate::leanh::lean_obj_tag(v___x_5663_) == 0 {
                    crate::leanh::lean_inc_ref(v_e_5629_);
                    v___x_5664_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_e_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_);
                    if crate::leanh::lean_obj_tag(v___x_5664_) == 0 {
                        v_a_5665_ = crate::leanh::lean_ctor_get(v___x_5664_, 0);
                        crate::leanh::lean_inc(v_a_5665_);
                        if crate::leanh::lean_obj_tag(v_a_5665_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5664_, 1);
                            v___x_5666_ = 0;
                            crate::leanh::lean_inc_ref(v_e_5629_);
                            v___x_5667_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(
                                v_e_5629_,
                                v___x_5666_,
                                v_a_5631_,
                                v_a_5632_,
                                v_a_5633_,
                                v_a_5634_,
                                v_a_5635_,
                            );
                            v___y_5638_ = v___x_5667_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_5665_, 1);
                            v___y_5638_ = v___x_5664_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_5638_ = v___x_5664_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5629_);
                    v_val_5668_ = crate::leanh::lean_ctor_get(v___x_5663_, 0);
                    v_isSharedCheck_5675_ = (!crate::leanh::lean_is_exclusive(v___x_5663_)) as u8;
                    if v_isSharedCheck_5675_ == 0 {
                        v___x_5670_ = v___x_5663_;
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5668_);
                        crate::leanh::lean_dec(v___x_5663_);
                        v___x_5670_ = crate::leanh::lean_box(0);
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5638_) == 0 {
                    v_a_5639_ = crate::leanh::lean_ctor_get(v___y_5638_, 0);
                    v_isSharedCheck_5660_ = (!crate::leanh::lean_is_exclusive(v___y_5638_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v___x_5641_ = v___y_5638_;
                        v_isShared_5642_ = v_isSharedCheck_5660_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5639_);
                        crate::leanh::lean_dec(v___y_5638_);
                        v___x_5641_ = crate::leanh::lean_box(0);
                        v_isShared_5642_ = v_isSharedCheck_5660_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_5629_);
                    return v___y_5638_;
                }
            }
            2 => {
                v___x_5643_ = lean_st_ref_take(v_a_5630_);
                v_lemmas_5644_ = crate::leanh::lean_ctor_get(v___x_5643_, 0);
                v_bvExprCache_5645_ = crate::leanh::lean_ctor_get(v___x_5643_, 1);
                v_bvPredCache_5646_ = crate::leanh::lean_ctor_get(v___x_5643_, 2);
                v_bvLogicalCache_5647_ = crate::leanh::lean_ctor_get(v___x_5643_, 3);
                v_isSharedCheck_5659_ = (!crate::leanh::lean_is_exclusive(v___x_5643_)) as u8;
                if v_isSharedCheck_5659_ == 0 {
                    v___x_5649_ = v___x_5643_;
                    v_isShared_5650_ = v_isSharedCheck_5659_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_bvLogicalCache_5647_);
                    crate::leanh::lean_inc(v_bvPredCache_5646_);
                    crate::leanh::lean_inc(v_bvExprCache_5645_);
                    crate::leanh::lean_inc(v_lemmas_5644_);
                    crate::leanh::lean_dec(v___x_5643_);
                    v___x_5649_ = crate::leanh::lean_box(0);
                    v_isShared_5650_ = v_isSharedCheck_5659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_5639_);
                v___x_5651_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvExprCache_5645_, v_e_5629_, v_a_5639_);
                if v_isShared_5650_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5649_, 1, v___x_5651_);
                    v___x_5653_ = v___x_5649_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5658_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_lemmas_5644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 1, v___x_5651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 2, v_bvPredCache_5646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 3, v_bvLogicalCache_5647_);
                    v___x_5653_ = v_reuseFailAlloc_5658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5654_ = lean_st_ref_set(v_a_5630_, v___x_5653_);
                if v_isShared_5642_ == 0 {
                    v___x_5656_ = v___x_5641_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5639_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5656_;
            }
            6 => {
                if v_isShared_5671_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5670_, 0);
                    v___x_5673_ = v___x_5670_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_val_5668_);
                    v___x_5673_ = v_reuseFailAlloc_5674_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(
    mut v_origExpr_5676_: *mut crate::leanh::LeanObject,
    mut v_a_5677_: *mut crate::leanh::LeanObject,
    mut v_a_5678_: *mut crate::leanh::LeanObject,
    mut v_a_5679_: *mut crate::leanh::LeanObject,
    mut v_a_5680_: *mut crate::leanh::LeanObject,
    mut v_a_5681_: *mut crate::leanh::LeanObject,
    mut v_a_5682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5684_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_origExpr_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_);
    return v___x_5684_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
    mut v_origExpr_5685_: *mut crate::leanh::LeanObject,
    mut v_a_5686_: *mut crate::leanh::LeanObject,
    mut v_a_5687_: *mut crate::leanh::LeanObject,
    mut v_a_5688_: *mut crate::leanh::LeanObject,
    mut v_a_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5693_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
    return v___x_5693_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of___boxed(
    mut v_origExpr_5694_: *mut crate::leanh::LeanObject,
    mut v_a_5695_: *mut crate::leanh::LeanObject,
    mut v_a_5696_: *mut crate::leanh::LeanObject,
    mut v_a_5697_: *mut crate::leanh::LeanObject,
    mut v_a_5698_: *mut crate::leanh::LeanObject,
    mut v_a_5699_: *mut crate::leanh::LeanObject,
    mut v_a_5700_: *mut crate::leanh::LeanObject,
    mut v_a_5701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5702_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
        v_origExpr_5694_,
        v_a_5695_,
        v_a_5696_,
        v_a_5697_,
        v_a_5698_,
        v_a_5699_,
        v_a_5700_,
    );
    crate::leanh::lean_dec(v_a_5700_);
    crate::leanh::lean_dec_ref(v_a_5699_);
    crate::leanh::lean_dec(v_a_5698_);
    crate::leanh::lean_dec_ref(v_a_5697_);
    crate::leanh::lean_dec(v_a_5696_);
    crate::leanh::lean_dec(v_a_5695_);
    return v_res_5702_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of___boxed(
    mut v_origExpr_5703_: *mut crate::leanh::LeanObject,
    mut v_a_5704_: *mut crate::leanh::LeanObject,
    mut v_a_5705_: *mut crate::leanh::LeanObject,
    mut v_a_5706_: *mut crate::leanh::LeanObject,
    mut v_a_5707_: *mut crate::leanh::LeanObject,
    mut v_a_5708_: *mut crate::leanh::LeanObject,
    mut v_a_5709_: *mut crate::leanh::LeanObject,
    mut v_a_5710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5711_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(
        v_origExpr_5703_,
        v_a_5704_,
        v_a_5705_,
        v_a_5706_,
        v_a_5707_,
        v_a_5708_,
        v_a_5709_,
    );
    crate::leanh::lean_dec(v_a_5709_);
    crate::leanh::lean_dec_ref(v_a_5708_);
    crate::leanh::lean_dec(v_a_5707_);
    crate::leanh::lean_dec_ref(v_a_5706_);
    crate::leanh::lean_dec(v_a_5705_);
    crate::leanh::lean_dec(v_a_5704_);
    return v_res_5711_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of___boxed(
    mut v_origExpr_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
    mut v_a_5714_: *mut crate::leanh::LeanObject,
    mut v_a_5715_: *mut crate::leanh::LeanObject,
    mut v_a_5716_: *mut crate::leanh::LeanObject,
    mut v_a_5717_: *mut crate::leanh::LeanObject,
    mut v_a_5718_: *mut crate::leanh::LeanObject,
    mut v_a_5719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5720_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(
        v_origExpr_5712_,
        v_a_5713_,
        v_a_5714_,
        v_a_5715_,
        v_a_5716_,
        v_a_5717_,
        v_a_5718_,
    );
    crate::leanh::lean_dec(v_a_5718_);
    crate::leanh::lean_dec_ref(v_a_5717_);
    crate::leanh::lean_dec(v_a_5716_);
    crate::leanh::lean_dec_ref(v_a_5715_);
    crate::leanh::lean_dec(v_a_5714_);
    crate::leanh::lean_dec(v_a_5713_);
    return v_res_5720_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom___boxed(
    mut v_origExpr_5721_: *mut crate::leanh::LeanObject,
    mut v_a_5722_: *mut crate::leanh::LeanObject,
    mut v_a_5723_: *mut crate::leanh::LeanObject,
    mut v_a_5724_: *mut crate::leanh::LeanObject,
    mut v_a_5725_: *mut crate::leanh::LeanObject,
    mut v_a_5726_: *mut crate::leanh::LeanObject,
    mut v_a_5727_: *mut crate::leanh::LeanObject,
    mut v_a_5728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5729_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
    crate::leanh::lean_dec(v_a_5727_);
    crate::leanh::lean_dec_ref(v_a_5726_);
    crate::leanh::lean_dec(v_a_5725_);
    crate::leanh::lean_dec_ref(v_a_5724_);
    crate::leanh::lean_dec(v_a_5723_);
    crate::leanh::lean_dec(v_a_5722_);
    return v_res_5729_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom___boxed(
    mut v_origExpr_5730_: *mut crate::leanh::LeanObject,
    mut v_a_5731_: *mut crate::leanh::LeanObject,
    mut v_a_5732_: *mut crate::leanh::LeanObject,
    mut v_a_5733_: *mut crate::leanh::LeanObject,
    mut v_a_5734_: *mut crate::leanh::LeanObject,
    mut v_a_5735_: *mut crate::leanh::LeanObject,
    mut v_a_5736_: *mut crate::leanh::LeanObject,
    mut v_a_5737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5738_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_);
    crate::leanh::lean_dec(v_a_5736_);
    crate::leanh::lean_dec_ref(v_a_5735_);
    crate::leanh::lean_dec(v_a_5734_);
    crate::leanh::lean_dec_ref(v_a_5733_);
    crate::leanh::lean_dec(v_a_5732_);
    crate::leanh::lean_dec(v_a_5731_);
    return v_res_5738_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection___boxed(
    mut v_distanceExpr_5739_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_5740_: *mut crate::leanh::LeanObject,
    mut v_rotateOp_5741_: *mut crate::leanh::LeanObject,
    mut v_rotateOpName_5742_: *mut crate::leanh::LeanObject,
    mut v_congrThm_5743_: *mut crate::leanh::LeanObject,
    mut v_origExpr_5744_: *mut crate::leanh::LeanObject,
    mut v_a_5745_: *mut crate::leanh::LeanObject,
    mut v_a_5746_: *mut crate::leanh::LeanObject,
    mut v_a_5747_: *mut crate::leanh::LeanObject,
    mut v_a_5748_: *mut crate::leanh::LeanObject,
    mut v_a_5749_: *mut crate::leanh::LeanObject,
    mut v_a_5750_: *mut crate::leanh::LeanObject,
    mut v_a_5751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5752_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_distanceExpr_5739_, v_innerExpr_5740_, v_rotateOp_5741_, v_rotateOpName_5742_, v_congrThm_5743_, v_origExpr_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_);
    crate::leanh::lean_dec(v_a_5750_);
    crate::leanh::lean_dec_ref(v_a_5749_);
    crate::leanh::lean_dec(v_a_5748_);
    crate::leanh::lean_dec_ref(v_a_5747_);
    crate::leanh::lean_dec(v_a_5746_);
    crate::leanh::lean_dec(v_a_5745_);
    crate::leanh::lean_dec_ref(v_distanceExpr_5739_);
    return v_res_5752_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred___boxed(
    mut v_origExpr_5753_: *mut crate::leanh::LeanObject,
    mut v_a_5754_: *mut crate::leanh::LeanObject,
    mut v_a_5755_: *mut crate::leanh::LeanObject,
    mut v_a_5756_: *mut crate::leanh::LeanObject,
    mut v_a_5757_: *mut crate::leanh::LeanObject,
    mut v_a_5758_: *mut crate::leanh::LeanObject,
    mut v_a_5759_: *mut crate::leanh::LeanObject,
    mut v_a_5760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5761_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
    crate::leanh::lean_dec(v_a_5759_);
    crate::leanh::lean_dec_ref(v_a_5758_);
    crate::leanh::lean_dec(v_a_5757_);
    crate::leanh::lean_dec_ref(v_a_5756_);
    crate::leanh::lean_dec(v_a_5755_);
    crate::leanh::lean_dec(v_a_5754_);
    return v_res_5761_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection___boxed(
    mut v_lhsExpr_5762_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_5763_: *mut crate::leanh::LeanObject,
    mut v_pred_5764_: *mut crate::leanh::LeanObject,
    mut v_origExpr_5765_: *mut crate::leanh::LeanObject,
    mut v_a_5766_: *mut crate::leanh::LeanObject,
    mut v_a_5767_: *mut crate::leanh::LeanObject,
    mut v_a_5768_: *mut crate::leanh::LeanObject,
    mut v_a_5769_: *mut crate::leanh::LeanObject,
    mut v_a_5770_: *mut crate::leanh::LeanObject,
    mut v_a_5771_: *mut crate::leanh::LeanObject,
    mut v_a_5772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pred_boxed_5773_: u8 = 0;
    let mut v_res_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pred_boxed_5773_ = (crate::leanh::lean_unbox(v_pred_5764_) as u8);
    v_res_5774_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_lhsExpr_5762_, v_rhsExpr_5763_, v_pred_boxed_5773_, v_origExpr_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
    crate::leanh::lean_dec(v_a_5771_);
    crate::leanh::lean_dec_ref(v_a_5770_);
    crate::leanh::lean_dec(v_a_5769_);
    crate::leanh::lean_dec_ref(v_a_5768_);
    crate::leanh::lean_dec(v_a_5767_);
    crate::leanh::lean_dec(v_a_5766_);
    return v_res_5774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection___boxed(
    mut v_lhsExpr_5775_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_5776_: *mut crate::leanh::LeanObject,
    mut v_gate_5777_: *mut crate::leanh::LeanObject,
    mut v_origExpr_5778_: *mut crate::leanh::LeanObject,
    mut v_a_5779_: *mut crate::leanh::LeanObject,
    mut v_a_5780_: *mut crate::leanh::LeanObject,
    mut v_a_5781_: *mut crate::leanh::LeanObject,
    mut v_a_5782_: *mut crate::leanh::LeanObject,
    mut v_a_5783_: *mut crate::leanh::LeanObject,
    mut v_a_5784_: *mut crate::leanh::LeanObject,
    mut v_a_5785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_boxed_5786_: u8 = 0;
    let mut v_res_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_gate_boxed_5786_ = (crate::leanh::lean_unbox(v_gate_5777_) as u8);
    v_res_5787_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_lhsExpr_5775_, v_rhsExpr_5776_, v_gate_boxed_5786_, v_origExpr_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_);
    crate::leanh::lean_dec(v_a_5784_);
    crate::leanh::lean_dec_ref(v_a_5783_);
    crate::leanh::lean_dec(v_a_5782_);
    crate::leanh::lean_dec_ref(v_a_5781_);
    crate::leanh::lean_dec(v_a_5780_);
    crate::leanh::lean_dec(v_a_5779_);
    return v_res_5787_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(
    mut v_distance_5788_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_5789_: *mut crate::leanh::LeanObject,
    mut v_shiftOp_5790_: *mut crate::leanh::LeanObject,
    mut v_shiftOpName_5791_: *mut crate::leanh::LeanObject,
    mut v_congrThm_5792_: *mut crate::leanh::LeanObject,
    mut v_origExpr_5793_: *mut crate::leanh::LeanObject,
    mut v_a_5794_: *mut crate::leanh::LeanObject,
    mut v_a_5795_: *mut crate::leanh::LeanObject,
    mut v_a_5796_: *mut crate::leanh::LeanObject,
    mut v_a_5797_: *mut crate::leanh::LeanObject,
    mut v_a_5798_: *mut crate::leanh::LeanObject,
    mut v_a_5799_: *mut crate::leanh::LeanObject,
    mut v_a_5800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5801_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_distance_5788_, v_innerExpr_5789_, v_shiftOp_5790_, v_shiftOpName_5791_, v_congrThm_5792_, v_origExpr_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_, v_a_5799_);
    crate::leanh::lean_dec(v_a_5799_);
    crate::leanh::lean_dec_ref(v_a_5798_);
    crate::leanh::lean_dec(v_a_5797_);
    crate::leanh::lean_dec_ref(v_a_5796_);
    crate::leanh::lean_dec(v_a_5795_);
    crate::leanh::lean_dec(v_a_5794_);
    return v_res_5801_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection___boxed(
    mut v_distanceExpr_5802_: *mut crate::leanh::LeanObject,
    mut v_innerExpr_5803_: *mut crate::leanh::LeanObject,
    mut v_shiftOp_5804_: *mut crate::leanh::LeanObject,
    mut v_shiftOpName_5805_: *mut crate::leanh::LeanObject,
    mut v_congrThm_5806_: *mut crate::leanh::LeanObject,
    mut v_origExpr_5807_: *mut crate::leanh::LeanObject,
    mut v_a_5808_: *mut crate::leanh::LeanObject,
    mut v_a_5809_: *mut crate::leanh::LeanObject,
    mut v_a_5810_: *mut crate::leanh::LeanObject,
    mut v_a_5811_: *mut crate::leanh::LeanObject,
    mut v_a_5812_: *mut crate::leanh::LeanObject,
    mut v_a_5813_: *mut crate::leanh::LeanObject,
    mut v_a_5814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5815_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_distanceExpr_5802_, v_innerExpr_5803_, v_shiftOp_5804_, v_shiftOpName_5805_, v_congrThm_5806_, v_origExpr_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_);
    crate::leanh::lean_dec(v_a_5813_);
    crate::leanh::lean_dec_ref(v_a_5812_);
    crate::leanh::lean_dec(v_a_5811_);
    crate::leanh::lean_dec_ref(v_a_5810_);
    crate::leanh::lean_dec(v_a_5809_);
    crate::leanh::lean_dec(v_a_5808_);
    return v_res_5815_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(
    mut v_e_5816_: *mut crate::leanh::LeanObject,
    mut v_a_5817_: *mut crate::leanh::LeanObject,
    mut v_a_5818_: *mut crate::leanh::LeanObject,
    mut v_a_5819_: *mut crate::leanh::LeanObject,
    mut v_a_5820_: *mut crate::leanh::LeanObject,
    mut v_a_5821_: *mut crate::leanh::LeanObject,
    mut v_a_5822_: *mut crate::leanh::LeanObject,
    mut v_a_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5824_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_e_5816_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_, v_a_5821_, v_a_5822_);
    crate::leanh::lean_dec(v_a_5822_);
    crate::leanh::lean_dec_ref(v_a_5821_);
    crate::leanh::lean_dec(v_a_5820_);
    crate::leanh::lean_dec_ref(v_a_5819_);
    crate::leanh::lean_dec(v_a_5818_);
    crate::leanh::lean_dec(v_a_5817_);
    return v_res_5824_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5___boxed(
    mut v_e_5825_: *mut crate::leanh::LeanObject,
    mut v_a_5826_: *mut crate::leanh::LeanObject,
    mut v_a_5827_: *mut crate::leanh::LeanObject,
    mut v_a_5828_: *mut crate::leanh::LeanObject,
    mut v_a_5829_: *mut crate::leanh::LeanObject,
    mut v_a_5830_: *mut crate::leanh::LeanObject,
    mut v_a_5831_: *mut crate::leanh::LeanObject,
    mut v_a_5832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5833_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(v_e_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_, v_a_5830_, v_a_5831_);
    crate::leanh::lean_dec(v_a_5831_);
    crate::leanh::lean_dec_ref(v_a_5830_);
    crate::leanh::lean_dec(v_a_5829_);
    crate::leanh::lean_dec_ref(v_a_5828_);
    crate::leanh::lean_dec(v_a_5827_);
    crate::leanh::lean_dec(v_a_5826_);
    return v_res_5833_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(
    mut v_e_5834_: *mut crate::leanh::LeanObject,
    mut v_a_5835_: *mut crate::leanh::LeanObject,
    mut v_a_5836_: *mut crate::leanh::LeanObject,
    mut v_a_5837_: *mut crate::leanh::LeanObject,
    mut v_a_5838_: *mut crate::leanh::LeanObject,
    mut v_a_5839_: *mut crate::leanh::LeanObject,
    mut v_a_5840_: *mut crate::leanh::LeanObject,
    mut v_a_5841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5842_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_e_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_);
    crate::leanh::lean_dec(v_a_5840_);
    crate::leanh::lean_dec_ref(v_a_5839_);
    crate::leanh::lean_dec(v_a_5838_);
    crate::leanh::lean_dec_ref(v_a_5837_);
    crate::leanh::lean_dec(v_a_5836_);
    crate::leanh::lean_dec(v_a_5835_);
    return v_res_5842_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___boxed(
    mut v_innerExpr_5843_: *mut crate::leanh::LeanObject,
    mut v_op_5844_: *mut crate::leanh::LeanObject,
    mut v_congrThm_5845_: *mut crate::leanh::LeanObject,
    mut v_origExpr_5846_: *mut crate::leanh::LeanObject,
    mut v_a_5847_: *mut crate::leanh::LeanObject,
    mut v_a_5848_: *mut crate::leanh::LeanObject,
    mut v_a_5849_: *mut crate::leanh::LeanObject,
    mut v_a_5850_: *mut crate::leanh::LeanObject,
    mut v_a_5851_: *mut crate::leanh::LeanObject,
    mut v_a_5852_: *mut crate::leanh::LeanObject,
    mut v_a_5853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5854_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_innerExpr_5843_, v_op_5844_, v_congrThm_5845_, v_origExpr_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_);
    crate::leanh::lean_dec(v_a_5852_);
    crate::leanh::lean_dec_ref(v_a_5851_);
    crate::leanh::lean_dec(v_a_5850_);
    crate::leanh::lean_dec_ref(v_a_5849_);
    crate::leanh::lean_dec(v_a_5848_);
    crate::leanh::lean_dec(v_a_5847_);
    return v_res_5854_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___boxed(
    mut v_lhsExpr_5855_: *mut crate::leanh::LeanObject,
    mut v_rhsExpr_5856_: *mut crate::leanh::LeanObject,
    mut v_op_5857_: *mut crate::leanh::LeanObject,
    mut v_congrThm_5858_: *mut crate::leanh::LeanObject,
    mut v_origExpr_5859_: *mut crate::leanh::LeanObject,
    mut v_a_5860_: *mut crate::leanh::LeanObject,
    mut v_a_5861_: *mut crate::leanh::LeanObject,
    mut v_a_5862_: *mut crate::leanh::LeanObject,
    mut v_a_5863_: *mut crate::leanh::LeanObject,
    mut v_a_5864_: *mut crate::leanh::LeanObject,
    mut v_a_5865_: *mut crate::leanh::LeanObject,
    mut v_a_5866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_boxed_5867_: u8 = 0;
    let mut v_res_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_op_boxed_5867_ = (crate::leanh::lean_unbox(v_op_5857_) as u8);
    v_res_5868_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_lhsExpr_5855_, v_rhsExpr_5856_, v_op_boxed_5867_, v_congrThm_5858_, v_origExpr_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_, v_a_5865_);
    crate::leanh::lean_dec(v_a_5865_);
    crate::leanh::lean_dec_ref(v_a_5864_);
    crate::leanh::lean_dec(v_a_5863_);
    crate::leanh::lean_dec_ref(v_a_5862_);
    crate::leanh::lean_dec(v_a_5861_);
    crate::leanh::lean_dec(v_a_5860_);
    return v_res_5868_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___boxed(
    mut v_origExpr_5869_: *mut crate::leanh::LeanObject,
    mut v_a_5870_: *mut crate::leanh::LeanObject,
    mut v_a_5871_: *mut crate::leanh::LeanObject,
    mut v_a_5872_: *mut crate::leanh::LeanObject,
    mut v_a_5873_: *mut crate::leanh::LeanObject,
    mut v_a_5874_: *mut crate::leanh::LeanObject,
    mut v_a_5875_: *mut crate::leanh::LeanObject,
    mut v_a_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5877_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_origExpr_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_);
    crate::leanh::lean_dec(v_a_5875_);
    crate::leanh::lean_dec_ref(v_a_5874_);
    crate::leanh::lean_dec(v_a_5873_);
    crate::leanh::lean_dec_ref(v_a_5872_);
    crate::leanh::lean_dec(v_a_5871_);
    crate::leanh::lean_dec(v_a_5870_);
    return v_res_5877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___boxed(
    mut v_origExpr_5878_: *mut crate::leanh::LeanObject,
    mut v_a_5879_: *mut crate::leanh::LeanObject,
    mut v_a_5880_: *mut crate::leanh::LeanObject,
    mut v_a_5881_: *mut crate::leanh::LeanObject,
    mut v_a_5882_: *mut crate::leanh::LeanObject,
    mut v_a_5883_: *mut crate::leanh::LeanObject,
    mut v_a_5884_: *mut crate::leanh::LeanObject,
    mut v_a_5885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5886_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_origExpr_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_);
    crate::leanh::lean_dec(v_a_5884_);
    crate::leanh::lean_dec_ref(v_a_5883_);
    crate::leanh::lean_dec(v_a_5882_);
    crate::leanh::lean_dec_ref(v_a_5881_);
    crate::leanh::lean_dec(v_a_5880_);
    crate::leanh::lean_dec(v_a_5879_);
    return v_res_5886_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___boxed(
    mut v_origExpr_5887_: *mut crate::leanh::LeanObject,
    mut v_a_5888_: *mut crate::leanh::LeanObject,
    mut v_a_5889_: *mut crate::leanh::LeanObject,
    mut v_a_5890_: *mut crate::leanh::LeanObject,
    mut v_a_5891_: *mut crate::leanh::LeanObject,
    mut v_a_5892_: *mut crate::leanh::LeanObject,
    mut v_a_5893_: *mut crate::leanh::LeanObject,
    mut v_a_5894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5895_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_origExpr_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
    crate::leanh::lean_dec(v_a_5893_);
    crate::leanh::lean_dec_ref(v_a_5892_);
    crate::leanh::lean_dec(v_a_5891_);
    crate::leanh::lean_dec_ref(v_a_5890_);
    crate::leanh::lean_dec(v_a_5889_);
    crate::leanh::lean_dec(v_a_5888_);
    return v_res_5895_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12(
    mut v_00_u03b1_5896_: *mut crate::leanh::LeanObject,
    mut v_msg_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
    mut v___y_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
    mut v___y_5903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5905_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_5897_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_);
    return v___x_5905_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___boxed(
    mut v_00_u03b1_5906_: *mut crate::leanh::LeanObject,
    mut v_msg_5907_: *mut crate::leanh::LeanObject,
    mut v___y_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
    mut v___y_5910_: *mut crate::leanh::LeanObject,
    mut v___y_5911_: *mut crate::leanh::LeanObject,
    mut v___y_5912_: *mut crate::leanh::LeanObject,
    mut v___y_5913_: *mut crate::leanh::LeanObject,
    mut v___y_5914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5915_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12(v_00_u03b1_5906_, v_msg_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_);
    crate::leanh::lean_dec(v___y_5913_);
    crate::leanh::lean_dec_ref(v___y_5912_);
    crate::leanh::lean_dec(v___y_5911_);
    crate::leanh::lean_dec_ref(v___y_5910_);
    crate::leanh::lean_dec(v___y_5909_);
    crate::leanh::lean_dec(v___y_5908_);
    return v_res_5915_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(
    mut v_00_u03b2_5916_: *mut crate::leanh::LeanObject,
    mut v_m_5917_: *mut crate::leanh::LeanObject,
    mut v_a_5918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_5917_, v_a_5918_);
    return v___x_5919_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(
    mut v_00_u03b2_5920_: *mut crate::leanh::LeanObject,
    mut v_m_5921_: *mut crate::leanh::LeanObject,
    mut v_a_5922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(v_00_u03b2_5920_, v_m_5921_, v_a_5922_);
    crate::leanh::lean_dec_ref(v_a_5922_);
    crate::leanh::lean_dec_ref(v_m_5921_);
    return v_res_5923_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(
    mut v_00_u03b2_5924_: *mut crate::leanh::LeanObject,
    mut v_m_5925_: *mut crate::leanh::LeanObject,
    mut v_a_5926_: *mut crate::leanh::LeanObject,
    mut v_b_5927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5928_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_m_5925_, v_a_5926_, v_b_5927_);
    return v___x_5928_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(
    mut v_00_u03b2_5929_: *mut crate::leanh::LeanObject,
    mut v_a_5930_: *mut crate::leanh::LeanObject,
    mut v_x_5931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5932_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_5930_, v_x_5931_);
    return v___x_5932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(
    mut v_00_u03b2_5933_: *mut crate::leanh::LeanObject,
    mut v_a_5934_: *mut crate::leanh::LeanObject,
    mut v_x_5935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5936_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(v_00_u03b2_5933_, v_a_5934_, v_x_5935_);
    crate::leanh::lean_dec(v_x_5935_);
    crate::leanh::lean_dec_ref(v_a_5934_);
    return v_res_5936_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(
    mut v_00_u03b2_5937_: *mut crate::leanh::LeanObject,
    mut v_a_5938_: *mut crate::leanh::LeanObject,
    mut v_x_5939_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5940_: u8 = 0;
    v___x_5940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_5938_, v_x_5939_);
    return v___x_5940_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(
    mut v_00_u03b2_5941_: *mut crate::leanh::LeanObject,
    mut v_a_5942_: *mut crate::leanh::LeanObject,
    mut v_x_5943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5944_: u8 = 0;
    let mut v_r_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5944_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(v_00_u03b2_5941_, v_a_5942_, v_x_5943_);
    crate::leanh::lean_dec(v_x_5943_);
    crate::leanh::lean_dec_ref(v_a_5942_);
    v_r_5945_ = crate::leanh::lean_box((v_res_5944_) as usize);
    return v_r_5945_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(
    mut v_00_u03b2_5946_: *mut crate::leanh::LeanObject,
    mut v_data_5947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5948_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_data_5947_);
    return v___x_5948_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(
    mut v_00_u03b2_5949_: *mut crate::leanh::LeanObject,
    mut v_a_5950_: *mut crate::leanh::LeanObject,
    mut v_b_5951_: *mut crate::leanh::LeanObject,
    mut v_x_5952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5953_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_5950_, v_b_5951_, v_x_5952_);
    return v___x_5953_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(
    mut v_00_u03b2_5954_: *mut crate::leanh::LeanObject,
    mut v_i_5955_: *mut crate::leanh::LeanObject,
    mut v_source_5956_: *mut crate::leanh::LeanObject,
    mut v_target_5957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5958_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v_i_5955_, v_source_5956_, v_target_5957_);
    return v___x_5958_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(
    mut v_00_u03b2_5959_: *mut crate::leanh::LeanObject,
    mut v_x_5960_: *mut crate::leanh::LeanObject,
    mut v_x_5961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5962_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_x_5960_, v_x_5961_);
    return v___x_5962_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
}
