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
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 102, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__1_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 112, 112, 101, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [114, 101, 112, 108, 105, 99, 97, 116, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 120, 116, 114, 97, 99, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [98, 118, 95, 100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 105, 116, 86, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 112, 111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value) as *mut leanh::LeanObject,13172393257619429686 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 108, 122, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value) as *mut leanh::LeanObject,15757622114771770429 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 118, 101, 114, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value) as *mut leanh::LeanObject,4526169109995817204 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value) as *mut leanh::LeanObject,7578295756008745317 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [114, 111, 116, 97, 116, 101, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value) as *mut leanh::LeanObject,11355947627665432272 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 111, 116, 97, 116, 101, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value) as *mut leanh::LeanObject,13324510433510274429 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 112, 108, 105, 99, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value) as *mut leanh::LeanObject,1452365453976042474 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value) as *mut leanh::LeanObject,10711138606260240846 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 109, 112, 108, 101, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 109, 112, 108, 101, 109, 101, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value) as *mut leanh::LeanObject,5724983336967091206 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value) as *mut leanh::LeanObject,12148653221863161512 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value) as *mut leanh::LeanObject,105488867511536770 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 120, 116, 114, 97, 99, 116, 76, 115, 98, 39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value) as *mut leanh::LeanObject,1678572690935040303 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [115, 115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 39, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value) as *mut leanh::LeanObject,7474321248668962373 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [104, 65, 112, 112, 101, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [72, 65, 112, 112, 101, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value) as *mut leanh::LeanObject,2304392498378253193 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value) as *mut leanh::LeanObject,16790970975024013749 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [72, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value) as *mut leanh::LeanObject,5422698995969631099 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value) as *mut leanh::LeanObject,11315714300293431604 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [72, 83, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value) as *mut leanh::LeanObject,12221703946232912343 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value) as *mut leanh::LeanObject,4302041416438838709 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value) as *mut leanh::LeanObject,13744984671752750173 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value) as *mut leanh::LeanObject,9682224670061807480 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value) as *mut leanh::LeanObject,11858238400308895562 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value) as *mut leanh::LeanObject,6100819061652633370 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value) as *mut leanh::LeanObject,1611444129324655608 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 88, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 88, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value) as *mut leanh::LeanObject,5661876967030703708 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value) as *mut leanh::LeanObject,11995384298059439981 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value) as *mut leanh::LeanObject,12657514296478584286 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value) as *mut leanh::LeanObject,14441402839729941302 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value) as *mut leanh::LeanObject,1264154450872014868 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 105, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 86, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value) as *mut leanh::LeanObject,1893448420036949551 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [66, 86, 66, 105, 110, 79, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject,2052334966301458605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value) as *mut leanh::LeanObject,8633590422926641219 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject,2052334966301458605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value) as *mut leanh::LeanObject,16739768336988840329 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [120, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject,2052334966301458605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value) as *mut leanh::LeanObject,12702694847026093380 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject,2052334966301458605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value) as *mut leanh::LeanObject,14273346465055528428 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [109, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject,2052334966301458605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value) as *mut leanh::LeanObject,5895671572980706882 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 100, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject,2052334966301458605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value) as *mut leanh::LeanObject,10337161908347300449 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 109, 111, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value) as *mut leanh::LeanObject,2052334966301458605 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value) as *mut leanh::LeanObject,799197807962006713 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [120, 111, 114, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value) as *mut leanh::LeanObject,4119725913644827105 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 100, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value) as *mut leanh::LeanObject,12822667666627757489 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 117, 108, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value) as *mut leanh::LeanObject,16232499424393338845 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 100, 105, 118, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value) as *mut leanh::LeanObject,2041225626295441782 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [117, 109, 111, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value) as *mut leanh::LeanObject,7562298844190415718 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 104, 105, 102, 116, 76, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value) as *mut leanh::LeanObject,6896204920017572293 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [115, 104, 105, 102, 116, 76, 101, 102, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value) as *mut leanh::LeanObject,8176945809791874937 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value: leanh::LeanStringObject<60> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 115, 104, 105, 102, 116, 32, 115, 104, 111, 117, 108, 100, 32, 104, 97, 118, 101, 32, 98, 101, 101, 110, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 100, 46, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_shiftRight___override as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value) as *mut leanh::LeanObject,16353154075727218503 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 104, 105, 102, 116, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value) as *mut leanh::LeanObject,7017916557232087512 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 101, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value) as *mut leanh::LeanObject,14769465239096254100 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value) as *mut leanh::LeanObject,9849265584244012391 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_value) as *mut leanh::LeanObject,11601345789416316724 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 120, 116, 114, 97, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value) as *mut leanh::LeanObject,646477182314419725 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value) as *mut leanh::LeanObject,15761733860085307253 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value) as *mut leanh::LeanObject,9255189395584251158 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [103, 101, 116, 76, 115, 98, 68, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value) as *mut leanh::LeanObject,5617647646599728841 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [117, 108, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,5394957827732845164 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value) as *mut leanh::LeanObject,17296090230036971119 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value) as *mut leanh::LeanObject,16093780639914376387 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value) as *mut leanh::LeanObject,9753356465987597394 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value) as *mut leanh::LeanObject,1655553077289932752 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value) as *mut leanh::LeanObject,10425341760733586335 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value) as *mut leanh::LeanObject,6148012076188572320 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value) as *mut leanh::LeanObject,12882480457794858234 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value) as *mut leanh::LeanObject,3186261684962074301 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [117, 110, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value) as *mut leanh::LeanObject,13103364627973585450 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [66, 86, 85, 110, 79, 112, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject,3440452707255258700 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value) as *mut leanh::LeanObject,5396454276475693598 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject,3440452707255258700 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value) as *mut leanh::LeanObject,9807480938810536989 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject,3440452707255258700 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value) as *mut leanh::LeanObject,18013547890344707440 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 67, 111, 110, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject,3440452707255258700 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value) as *mut leanh::LeanObject,15020990588075728728 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject,3440452707255258700 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value) as *mut leanh::LeanObject,13041317507303989844 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject,3440452707255258700 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value) as *mut leanh::LeanObject,744326716584575709 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value) as *mut leanh::LeanObject,3440452707255258700 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value) as *mut leanh::LeanObject,4313869223568439254 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [97, 114, 105, 116, 104, 83, 104, 105, 102, 116, 82, 105, 103, 104, 116, 78, 97, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value) as *mut leanh::LeanObject,11604326280315543611 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value) as *mut leanh::LeanObject,14410340039599863083 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value) as *mut leanh::LeanObject,11468030476923802729 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [114, 111, 116, 97, 116, 101, 76, 101, 102, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_value) as *mut leanh::LeanObject,4477786134226854944 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 111, 116, 97, 116, 101, 82, 105, 103, 104, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value) as *mut leanh::LeanObject,3973774320290730301 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [114, 101, 118, 101, 114, 115, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value) as *mut leanh::LeanObject,6433797635050614710 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 108, 122, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value) as *mut leanh::LeanObject,9523836033625423468 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 112, 111, 112, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value) as *mut leanh::LeanObject,15734321041234825264 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value) as *mut leanh::LeanObject,5139300886809190733 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value) as *mut leanh::LeanObject,17363264175708149920 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___closed__0_value) as *mut leanh::LeanObject,18076273821967539232 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value) as *mut leanh::LeanObject,403369037444587699 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value) as *mut leanh::LeanObject,16094149021198470069 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(
    mut v_x_2982_: *mut leanh::LeanObject,
    mut v_a_2983_: *mut leanh::LeanObject,
    mut v_a_2984_: *mut leanh::LeanObject,
    mut v_a_2985_: *mut leanh::LeanObject,
    mut v_a_2986_: *mut leanh::LeanObject,
    mut v_a_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v_fst_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut v_a_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3012_: u8 = 0;
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3016_: u8 = 0;
    let mut v_isSharedCheck_3017_: u8 = 0;
    let mut v___x_3018_: u8 = 0;
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_x_2982_);
                v___x_2989_ = l_Lean_Meta_getBitVecValue_x3f(
                    v_x_2982_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_,
                );
                if leanh::lean_obj_tag(v___x_2989_) == 0 {
                    v_a_2990_ = leanh::lean_ctor_get(v___x_2989_, 0);
                    leanh::lean_inc(v_a_2990_);
                    leanh::lean_dec_ref_known(v___x_2989_, 1);
                    if leanh::lean_obj_tag(v_a_2990_) == 1 {
                        leanh::lean_dec_ref(v_x_2982_);
                        v_val_2991_ = leanh::lean_ctor_get(v_a_2990_, 0);
                        v_isSharedCheck_3017_ = (!leanh::lean_is_exclusive(v_a_2990_)) as u8;
                        if v_isSharedCheck_3017_ == 0 {
                            v___x_2993_ = v_a_2990_;
                            v_isShared_2994_ = v_isSharedCheck_3017_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2991_);
                            leanh::lean_dec(v_a_2990_);
                            v___x_2993_ = leanh::lean_box(0);
                            v_isShared_2994_ = v_isSharedCheck_3017_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2990_);
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
                    leanh::lean_dec_ref(v_x_2982_);
                    v_a_3020_ = leanh::lean_ctor_get(v___x_2989_, 0);
                    v_isSharedCheck_3027_ = (!leanh::lean_is_exclusive(v___x_2989_)) as u8;
                    if v_isSharedCheck_3027_ == 0 {
                        v___x_3022_ = v___x_2989_;
                        v_isShared_3023_ = v_isSharedCheck_3027_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3020_);
                        leanh::lean_dec(v___x_2989_);
                        v___x_3022_ = leanh::lean_box(0);
                        v_isShared_3023_ = v_isSharedCheck_3027_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2995_ = leanh::lean_ctor_get(v_val_2991_, 0);
                leanh::lean_inc(v_fst_2995_);
                v_snd_2996_ = leanh::lean_ctor_get(v_val_2991_, 1);
                leanh::lean_inc(v_snd_2996_);
                leanh::lean_dec(v_val_2991_);
                v___x_2997_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(
                    v_fst_2995_,
                    v_snd_2996_,
                );
                if leanh::lean_obj_tag(v___x_2997_) == 0 {
                    v_a_2998_ = leanh::lean_ctor_get(v___x_2997_, 0);
                    v_isSharedCheck_3008_ = (!leanh::lean_is_exclusive(v___x_2997_)) as u8;
                    if v_isSharedCheck_3008_ == 0 {
                        v___x_3000_ = v___x_2997_;
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2998_);
                        leanh::lean_dec(v___x_2997_);
                        v___x_3000_ = leanh::lean_box(0);
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2993_);
                    v_a_3009_ = leanh::lean_ctor_get(v___x_2997_, 0);
                    v_isSharedCheck_3016_ = (!leanh::lean_is_exclusive(v___x_2997_)) as u8;
                    if v_isSharedCheck_3016_ == 0 {
                        v___x_3011_ = v___x_2997_;
                        v_isShared_3012_ = v_isSharedCheck_3016_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3009_);
                        leanh::lean_dec(v___x_2997_);
                        v___x_3011_ = leanh::lean_box(0);
                        v_isShared_3012_ = v_isSharedCheck_3016_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2994_ == 0 {
                    leanh::lean_ctor_set(v___x_2993_, 0, v_a_2998_);
                    v___x_3003_ = v___x_2993_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3007_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3007_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3001_ == 0 {
                    leanh::lean_ctor_set(v___x_3000_, 0, v___x_3003_);
                    v___x_3005_ = v___x_3000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
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
                    v_reuseFailAlloc_3015_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
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
                    v_reuseFailAlloc_3026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
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
    mut v_x_3028_: *mut leanh::LeanObject,
    mut v_a_3029_: *mut leanh::LeanObject,
    mut v_a_3030_: *mut leanh::LeanObject,
    mut v_a_3031_: *mut leanh::LeanObject,
    mut v_a_3032_: *mut leanh::LeanObject,
    mut v_a_3033_: *mut leanh::LeanObject,
    mut v_a_3034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3035_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_x_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_);
    leanh::lean_dec(v_a_3033_);
    leanh::lean_dec_ref(v_a_3032_);
    leanh::lean_dec(v_a_3031_);
    leanh::lean_dec_ref(v_a_3030_);
    leanh::lean_dec(v_a_3029_);
    return v_res_3035_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(
    mut v___x_3036_: *mut leanh::LeanObject,
    mut v_fst_3037_: *mut leanh::LeanObject,
    mut v_fproof_3038_: *mut leanh::LeanObject,
    mut v_snd_3039_: *mut leanh::LeanObject,
    mut v_sproof_3040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3051_: u8 = 0;
    let mut v_val_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3055_: u8 = 0;
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut v_val_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3066_: u8 = 0;
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_fproof_3038_) == 0 {
                    leanh::lean_dec_ref(v_snd_3039_);
                    if leanh::lean_obj_tag(v_sproof_3040_) == 0 {
                        leanh::lean_dec_ref(v_fst_3037_);
                        leanh::lean_dec(v___x_3036_);
                        v___x_3041_ = leanh::lean_box(0);
                        return v___x_3041_;
                    } else {
                        v_val_3042_ = leanh::lean_ctor_get(v_sproof_3040_, 0);
                        v_isSharedCheck_3051_ =
                            (!leanh::lean_is_exclusive(v_sproof_3040_)) as u8;
                        if v_isSharedCheck_3051_ == 0 {
                            v___x_3044_ = v_sproof_3040_;
                            v_isShared_3045_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3042_);
                            leanh::lean_dec(v_sproof_3040_);
                            v___x_3044_ = leanh::lean_box(0);
                            v_isShared_3045_ = v_isSharedCheck_3051_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fst_3037_);
                    if leanh::lean_obj_tag(v_sproof_3040_) == 0 {
                        v_val_3052_ = leanh::lean_ctor_get(v_fproof_3038_, 0);
                        v_isSharedCheck_3061_ =
                            (!leanh::lean_is_exclusive(v_fproof_3038_)) as u8;
                        if v_isSharedCheck_3061_ == 0 {
                            v___x_3054_ = v_fproof_3038_;
                            v_isShared_3055_ = v_isSharedCheck_3061_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3052_);
                            leanh::lean_dec(v_fproof_3038_);
                            v___x_3054_ = leanh::lean_box(0);
                            v_isShared_3055_ = v_isSharedCheck_3061_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_snd_3039_);
                        leanh::lean_dec(v___x_3036_);
                        v_val_3062_ = leanh::lean_ctor_get(v_fproof_3038_, 0);
                        leanh::lean_inc(v_val_3062_);
                        leanh::lean_dec_ref_known(v_fproof_3038_, 1);
                        v_val_3063_ = leanh::lean_ctor_get(v_sproof_3040_, 0);
                        v_isSharedCheck_3071_ =
                            (!leanh::lean_is_exclusive(v_sproof_3040_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_3065_ = v_sproof_3040_;
                            v_isShared_3066_ = v_isSharedCheck_3071_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3063_);
                            leanh::lean_dec(v_sproof_3040_);
                            v___x_3065_ = leanh::lean_box(0);
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
                v___x_3047_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3047_, 0, v___x_3046_);
                leanh::lean_ctor_set(v___x_3047_, 1, v_val_3042_);
                if v_isShared_3045_ == 0 {
                    leanh::lean_ctor_set(v___x_3044_, 0, v___x_3047_);
                    v___x_3049_ = v___x_3044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
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
                v___x_3057_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3057_, 0, v_val_3052_);
                leanh::lean_ctor_set(v___x_3057_, 1, v___x_3056_);
                if v_isShared_3055_ == 0 {
                    leanh::lean_ctor_set(v___x_3054_, 0, v___x_3057_);
                    v___x_3059_ = v___x_3054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
                    v___x_3059_ = v_reuseFailAlloc_3060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3059_;
            }
            5 => {
                v___x_3067_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3067_, 0, v_val_3062_);
                leanh::lean_ctor_set(v___x_3067_, 1, v_val_3063_);
                if v_isShared_3066_ == 0 {
                    leanh::lean_ctor_set(v___x_3065_, 0, v___x_3067_);
                    v___x_3069_ = v___x_3065_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
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
    mut v_lhs_3072_: *mut leanh::LeanObject,
    mut v_rhs_3073_: *mut leanh::LeanObject,
    mut v_lhsExpr_3074_: *mut leanh::LeanObject,
    mut v_rhsExpr_3075_: *mut leanh::LeanObject,
    mut v_congrThm_3076_: *mut leanh::LeanObject,
    mut v_a_3077_: *mut leanh::LeanObject,
    mut v_a_3078_: *mut leanh::LeanObject,
    mut v_a_3079_: *mut leanh::LeanObject,
    mut v_a_3080_: *mut leanh::LeanObject,
    mut v_a_3081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_width_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v_fst_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3112_: u8 = 0;
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3117_: u8 = 0;
    let mut v_a_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3121_: u8 = 0;
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3125_: u8 = 0;
    let mut v_a_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_width_3083_ = leanh::lean_ctor_get(v_lhs_3072_, 0);
                leanh::lean_inc_n(v_width_3083_, 2);
                v_expr_3084_ = leanh::lean_ctor_get(v_lhs_3072_, 4);
                leanh::lean_inc_ref(v_expr_3084_);
                v___x_3085_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3083_,
                    v_expr_3084_,
                    v_a_3077_,
                    v_a_3078_,
                    v_a_3079_,
                    v_a_3080_,
                    v_a_3081_,
                );
                if leanh::lean_obj_tag(v___x_3085_) == 0 {
                    v_a_3086_ = leanh::lean_ctor_get(v___x_3085_, 0);
                    leanh::lean_inc(v_a_3086_);
                    leanh::lean_dec_ref_known(v___x_3085_, 1);
                    v_width_3087_ = leanh::lean_ctor_get(v_rhs_3073_, 0);
                    v_expr_3088_ = leanh::lean_ctor_get(v_rhs_3073_, 4);
                    leanh::lean_inc_ref(v_expr_3088_);
                    leanh::lean_inc(v_width_3087_);
                    v___x_3089_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                        v_width_3087_,
                        v_expr_3088_,
                        v_a_3077_,
                        v_a_3078_,
                        v_a_3079_,
                        v_a_3080_,
                        v_a_3081_,
                    );
                    if leanh::lean_obj_tag(v___x_3089_) == 0 {
                        v_a_3090_ = leanh::lean_ctor_get(v___x_3089_, 0);
                        leanh::lean_inc(v_a_3090_);
                        leanh::lean_dec_ref_known(v___x_3089_, 1);
                        v___x_3091_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                            v_lhs_3072_,
                            v_a_3077_,
                            v_a_3078_,
                            v_a_3079_,
                            v_a_3080_,
                            v_a_3081_,
                        );
                        if leanh::lean_obj_tag(v___x_3091_) == 0 {
                            v_a_3092_ = leanh::lean_ctor_get(v___x_3091_, 0);
                            leanh::lean_inc(v_a_3092_);
                            leanh::lean_dec_ref_known(v___x_3091_, 1);
                            v___x_3093_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                                v_rhs_3073_,
                                v_a_3077_,
                                v_a_3078_,
                                v_a_3079_,
                                v_a_3080_,
                                v_a_3081_,
                            );
                            if leanh::lean_obj_tag(v___x_3093_) == 0 {
                                v_a_3094_ = leanh::lean_ctor_get(v___x_3093_, 0);
                                v_isSharedCheck_3117_ =
                                    (!leanh::lean_is_exclusive(v___x_3093_)) as u8;
                                if v_isSharedCheck_3117_ == 0 {
                                    v___x_3096_ = v___x_3093_;
                                    v_isShared_3097_ = v_isSharedCheck_3117_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3094_);
                                    leanh::lean_dec(v___x_3093_);
                                    v___x_3096_ = leanh::lean_box(0);
                                    v_isShared_3097_ = v_isSharedCheck_3117_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_3092_);
                                leanh::lean_dec(v_a_3090_);
                                leanh::lean_dec(v_a_3086_);
                                leanh::lean_dec(v_width_3083_);
                                leanh::lean_dec_ref(v_congrThm_3076_);
                                leanh::lean_dec_ref(v_rhsExpr_3075_);
                                leanh::lean_dec_ref(v_lhsExpr_3074_);
                                return v___x_3093_;
                            }
                        } else {
                            leanh::lean_dec(v_a_3090_);
                            leanh::lean_dec(v_a_3086_);
                            leanh::lean_dec(v_width_3083_);
                            leanh::lean_dec_ref(v_congrThm_3076_);
                            leanh::lean_dec_ref(v_rhsExpr_3075_);
                            leanh::lean_dec_ref(v_lhsExpr_3074_);
                            leanh::lean_dec_ref(v_rhs_3073_);
                            return v___x_3091_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3086_);
                        leanh::lean_dec(v_width_3083_);
                        leanh::lean_dec_ref(v_congrThm_3076_);
                        leanh::lean_dec_ref(v_rhsExpr_3075_);
                        leanh::lean_dec_ref(v_lhsExpr_3074_);
                        leanh::lean_dec_ref(v_rhs_3073_);
                        leanh::lean_dec_ref(v_lhs_3072_);
                        v_a_3118_ = leanh::lean_ctor_get(v___x_3089_, 0);
                        v_isSharedCheck_3125_ =
                            (!leanh::lean_is_exclusive(v___x_3089_)) as u8;
                        if v_isSharedCheck_3125_ == 0 {
                            v___x_3120_ = v___x_3089_;
                            v_isShared_3121_ = v_isSharedCheck_3125_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3118_);
                            leanh::lean_dec(v___x_3089_);
                            v___x_3120_ = leanh::lean_box(0);
                            v_isShared_3121_ = v_isSharedCheck_3125_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_width_3083_);
                    leanh::lean_dec_ref(v_congrThm_3076_);
                    leanh::lean_dec_ref(v_rhsExpr_3075_);
                    leanh::lean_dec_ref(v_lhsExpr_3074_);
                    leanh::lean_dec_ref(v_rhs_3073_);
                    leanh::lean_dec_ref(v_lhs_3072_);
                    v_a_3126_ = leanh::lean_ctor_get(v___x_3085_, 0);
                    v_isSharedCheck_3133_ = (!leanh::lean_is_exclusive(v___x_3085_)) as u8;
                    if v_isSharedCheck_3133_ == 0 {
                        v___x_3128_ = v___x_3085_;
                        v_isShared_3129_ = v_isSharedCheck_3133_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3126_);
                        leanh::lean_dec(v___x_3085_);
                        v___x_3128_ = leanh::lean_box(0);
                        v_isShared_3129_ = v_isSharedCheck_3133_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_3090_);
                leanh::lean_inc(v_a_3086_);
                v___x_3098_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(v_width_3083_, v_a_3086_, v_a_3092_, v_a_3090_, v_a_3094_);
                if leanh::lean_obj_tag(v___x_3098_) == 1 {
                    v_val_3099_ = leanh::lean_ctor_get(v___x_3098_, 0);
                    v_isSharedCheck_3112_ = (!leanh::lean_is_exclusive(v___x_3098_)) as u8;
                    if v_isSharedCheck_3112_ == 0 {
                        v___x_3101_ = v___x_3098_;
                        v_isShared_3102_ = v_isSharedCheck_3112_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3099_);
                        leanh::lean_dec(v___x_3098_);
                        v___x_3101_ = leanh::lean_box(0);
                        v_isShared_3102_ = v_isSharedCheck_3112_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3098_);
                    leanh::lean_dec(v_a_3090_);
                    leanh::lean_dec(v_a_3086_);
                    leanh::lean_dec_ref(v_congrThm_3076_);
                    leanh::lean_dec_ref(v_rhsExpr_3075_);
                    leanh::lean_dec_ref(v_lhsExpr_3074_);
                    v___x_3113_ = leanh::lean_box(0);
                    if v_isShared_3097_ == 0 {
                        leanh::lean_ctor_set(v___x_3096_, 0, v___x_3113_);
                        v___x_3115_ = v___x_3096_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3113_);
                        v___x_3115_ = v_reuseFailAlloc_3116_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3103_ = leanh::lean_ctor_get(v_val_3099_, 0);
                leanh::lean_inc(v_fst_3103_);
                v_snd_3104_ = leanh::lean_ctor_get(v_val_3099_, 1);
                leanh::lean_inc(v_snd_3104_);
                leanh::lean_dec(v_val_3099_);
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
                    leanh::lean_ctor_set(v___x_3101_, 0, v___x_3105_);
                    v___x_3107_ = v___x_3101_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3111_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3097_ == 0 {
                    leanh::lean_ctor_set(v___x_3096_, 0, v___x_3107_);
                    v___x_3109_ = v___x_3096_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3107_);
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
                    v_reuseFailAlloc_3124_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
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
                    v_reuseFailAlloc_3132_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
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
    mut v_lhs_3134_: *mut leanh::LeanObject,
    mut v_rhs_3135_: *mut leanh::LeanObject,
    mut v_lhsExpr_3136_: *mut leanh::LeanObject,
    mut v_rhsExpr_3137_: *mut leanh::LeanObject,
    mut v_congrThm_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
    mut v_a_3142_: *mut leanh::LeanObject,
    mut v_a_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3145_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(v_lhs_3134_, v_rhs_3135_, v_lhsExpr_3136_, v_rhsExpr_3137_, v_congrThm_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_);
    leanh::lean_dec(v_a_3143_);
    leanh::lean_dec_ref(v_a_3142_);
    leanh::lean_dec(v_a_3141_);
    leanh::lean_dec_ref(v_a_3140_);
    leanh::lean_dec(v_a_3139_);
    return v_res_3145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(
    mut v_inner_3146_: *mut leanh::LeanObject,
    mut v_innerExpr_3147_: *mut leanh::LeanObject,
    mut v_congrProof_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
    mut v_a_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
    mut v_a_3153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_width_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3163_: u8 = 0;
    let mut v_val_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3167_: u8 = 0;
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v_a_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_width_3155_ = leanh::lean_ctor_get(v_inner_3146_, 0);
                leanh::lean_inc_n(v_width_3155_, 2);
                v_expr_3156_ = leanh::lean_ctor_get(v_inner_3146_, 4);
                leanh::lean_inc_ref(v_expr_3156_);
                v___x_3157_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3155_,
                    v_expr_3156_,
                    v_a_3149_,
                    v_a_3150_,
                    v_a_3151_,
                    v_a_3152_,
                    v_a_3153_,
                );
                if leanh::lean_obj_tag(v___x_3157_) == 0 {
                    v_a_3158_ = leanh::lean_ctor_get(v___x_3157_, 0);
                    leanh::lean_inc(v_a_3158_);
                    leanh::lean_dec_ref_known(v___x_3157_, 1);
                    v___x_3159_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                        v_inner_3146_,
                        v_a_3149_,
                        v_a_3150_,
                        v_a_3151_,
                        v_a_3152_,
                        v_a_3153_,
                    );
                    if leanh::lean_obj_tag(v___x_3159_) == 0 {
                        v_a_3160_ = leanh::lean_ctor_get(v___x_3159_, 0);
                        v_isSharedCheck_3181_ =
                            (!leanh::lean_is_exclusive(v___x_3159_)) as u8;
                        if v_isSharedCheck_3181_ == 0 {
                            v___x_3162_ = v___x_3159_;
                            v_isShared_3163_ = v_isSharedCheck_3181_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3160_);
                            leanh::lean_dec(v___x_3159_);
                            v___x_3162_ = leanh::lean_box(0);
                            v_isShared_3163_ = v_isSharedCheck_3181_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3158_);
                        leanh::lean_dec(v_width_3155_);
                        leanh::lean_dec_ref(v_congrProof_3148_);
                        leanh::lean_dec_ref(v_innerExpr_3147_);
                        return v___x_3159_;
                    }
                } else {
                    leanh::lean_dec(v_width_3155_);
                    leanh::lean_dec_ref(v_congrProof_3148_);
                    leanh::lean_dec_ref(v_innerExpr_3147_);
                    leanh::lean_dec_ref(v_inner_3146_);
                    v_a_3182_ = leanh::lean_ctor_get(v___x_3157_, 0);
                    v_isSharedCheck_3189_ = (!leanh::lean_is_exclusive(v___x_3157_)) as u8;
                    if v_isSharedCheck_3189_ == 0 {
                        v___x_3184_ = v___x_3157_;
                        v_isShared_3185_ = v_isSharedCheck_3189_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3182_);
                        leanh::lean_dec(v___x_3157_);
                        v___x_3184_ = leanh::lean_box(0);
                        v_isShared_3185_ = v_isSharedCheck_3189_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3160_) == 1 {
                    v_val_3164_ = leanh::lean_ctor_get(v_a_3160_, 0);
                    v_isSharedCheck_3176_ = (!leanh::lean_is_exclusive(v_a_3160_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3166_ = v_a_3160_;
                        v_isShared_3167_ = v_isSharedCheck_3176_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3164_);
                        leanh::lean_dec(v_a_3160_);
                        v___x_3166_ = leanh::lean_box(0);
                        v_isShared_3167_ = v_isSharedCheck_3176_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3160_);
                    leanh::lean_dec(v_a_3158_);
                    leanh::lean_dec(v_width_3155_);
                    leanh::lean_dec_ref(v_congrProof_3148_);
                    leanh::lean_dec_ref(v_innerExpr_3147_);
                    v___x_3177_ = leanh::lean_box(0);
                    if v_isShared_3163_ == 0 {
                        leanh::lean_ctor_set(v___x_3162_, 0, v___x_3177_);
                        v___x_3179_ = v___x_3162_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
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
                    leanh::lean_ctor_set(v___x_3166_, 0, v___x_3169_);
                    v___x_3171_ = v___x_3166_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3169_);
                    v___x_3171_ = v_reuseFailAlloc_3175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3163_ == 0 {
                    leanh::lean_ctor_set(v___x_3162_, 0, v___x_3171_);
                    v___x_3173_ = v___x_3162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3174_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
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
                    v_reuseFailAlloc_3188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
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
    mut v_inner_3190_: *mut leanh::LeanObject,
    mut v_innerExpr_3191_: *mut leanh::LeanObject,
    mut v_congrProof_3192_: *mut leanh::LeanObject,
    mut v_a_3193_: *mut leanh::LeanObject,
    mut v_a_3194_: *mut leanh::LeanObject,
    mut v_a_3195_: *mut leanh::LeanObject,
    mut v_a_3196_: *mut leanh::LeanObject,
    mut v_a_3197_: *mut leanh::LeanObject,
    mut v_a_3198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3199_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(v_inner_3190_, v_innerExpr_3191_, v_congrProof_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
    leanh::lean_dec(v_a_3197_);
    leanh::lean_dec_ref(v_a_3196_);
    leanh::lean_dec(v_a_3195_);
    leanh::lean_dec_ref(v_a_3194_);
    leanh::lean_dec(v_a_3193_);
    return v_res_3199_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(
    mut v_a_3200_: *mut leanh::LeanObject,
    mut v_x_3201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3201_) == 0 {
                    v___x_3202_ = leanh::lean_box(0);
                    return v___x_3202_;
                } else {
                    v_key_3203_ = leanh::lean_ctor_get(v_x_3201_, 0);
                    v_value_3204_ = leanh::lean_ctor_get(v_x_3201_, 1);
                    v_tail_3205_ = leanh::lean_ctor_get(v_x_3201_, 2);
                    v___x_3206_ = lean_expr_eqv(v_key_3203_, v_a_3200_);
                    if v___x_3206_ == 0 {
                        v_x_3201_ = v_tail_3205_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3204_);
                        v___x_3208_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3208_, 0, v_value_3204_);
                        return v___x_3208_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(
    mut v_a_3209_: *mut leanh::LeanObject,
    mut v_x_3210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3211_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_3209_, v_x_3210_);
    leanh::lean_dec(v_x_3210_);
    leanh::lean_dec_ref(v_a_3209_);
    return v_res_3211_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(
    mut v_m_3212_: *mut leanh::LeanObject,
    mut v_a_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3214_ = leanh::lean_ctor_get(v_m_3212_, 1);
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
    mut v_m_3230_: *mut leanh::LeanObject,
    mut v_a_3231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3232_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_3230_, v_a_3231_);
    leanh::lean_dec_ref(v_a_3231_);
    leanh::lean_dec_ref(v_m_3230_);
    return v_res_3232_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(
    mut v_x_3233_: *mut leanh::LeanObject,
    mut v_x_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3234_) == 0 {
                    return v_x_3233_;
                } else {
                    v_key_3235_ = leanh::lean_ctor_get(v_x_3234_, 0);
                    v_value_3236_ = leanh::lean_ctor_get(v_x_3234_, 1);
                    v_tail_3237_ = leanh::lean_ctor_get(v_x_3234_, 2);
                    v_isSharedCheck_3260_ = (!leanh::lean_is_exclusive(v_x_3234_)) as u8;
                    if v_isSharedCheck_3260_ == 0 {
                        v___x_3239_ = v_x_3234_;
                        v_isShared_3240_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3237_);
                        leanh::lean_inc(v_value_3236_);
                        leanh::lean_inc(v_key_3235_);
                        leanh::lean_dec(v_x_3234_);
                        v___x_3239_ = leanh::lean_box(0);
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
                leanh::lean_inc(v___x_3254_);
                if v_isShared_3240_ == 0 {
                    leanh::lean_ctor_set(v___x_3239_, 2, v___x_3254_);
                    v___x_3256_ = v___x_3239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_key_3235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 1, v_value_3236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 2, v___x_3254_);
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
    mut v_i_3261_: *mut leanh::LeanObject,
    mut v_source_3262_: *mut leanh::LeanObject,
    mut v_target_3263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: u8 = 0;
    let mut v_es_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3264_ = lean_array_get_size(v_source_3262_);
                v___x_3265_ = lean_nat_dec_lt(v_i_3261_, v___x_3264_);
                if v___x_3265_ == 0 {
                    leanh::lean_dec_ref(v_source_3262_);
                    leanh::lean_dec(v_i_3261_);
                    return v_target_3263_;
                } else {
                    v_es_3266_ = lean_array_fget(v_source_3262_, v_i_3261_);
                    v___x_3267_ = leanh::lean_box(0);
                    v_source_3268_ = lean_array_fset(v_source_3262_, v_i_3261_, v___x_3267_);
                    v_target_3269_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_target_3263_, v_es_3266_);
                    v___x_3270_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3271_ = lean_nat_add(v_i_3261_, v___x_3270_);
                    leanh::lean_dec(v_i_3261_);
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
    mut v_data_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = lean_array_get_size(v_data_3273_);
    v___x_3275_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3276_ = lean_nat_mul(v___x_3274_, v___x_3275_);
    v___x_3277_ = leanh::lean_unsigned_to_nat(0);
    v___x_3278_ = leanh::lean_box(0);
    v___x_3279_ = lean_mk_array(v_nbuckets_3276_, v___x_3278_);
    v___x_3280_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v___x_3277_, v_data_3273_, v___x_3279_);
    return v___x_3280_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(
    mut v_a_3281_: *mut leanh::LeanObject,
    mut v_b_3282_: *mut leanh::LeanObject,
    mut v_x_3283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3289_: u8 = 0;
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3283_) == 0 {
                    leanh::lean_dec(v_b_3282_);
                    leanh::lean_dec_ref(v_a_3281_);
                    return v_x_3283_;
                } else {
                    v_key_3284_ = leanh::lean_ctor_get(v_x_3283_, 0);
                    v_value_3285_ = leanh::lean_ctor_get(v_x_3283_, 1);
                    v_tail_3286_ = leanh::lean_ctor_get(v_x_3283_, 2);
                    v_isSharedCheck_3298_ = (!leanh::lean_is_exclusive(v_x_3283_)) as u8;
                    if v_isSharedCheck_3298_ == 0 {
                        v___x_3288_ = v_x_3283_;
                        v_isShared_3289_ = v_isSharedCheck_3298_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3286_);
                        leanh::lean_inc(v_value_3285_);
                        leanh::lean_inc(v_key_3284_);
                        leanh::lean_dec(v_x_3283_);
                        v___x_3288_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_3288_, 2, v___x_3291_);
                        v___x_3293_ = v___x_3288_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3294_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_key_3284_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_value_3285_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 2, v___x_3291_);
                        v___x_3293_ = v_reuseFailAlloc_3294_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_3285_);
                    leanh::lean_dec(v_key_3284_);
                    if v_isShared_3289_ == 0 {
                        leanh::lean_ctor_set(v___x_3288_, 1, v_b_3282_);
                        leanh::lean_ctor_set(v___x_3288_, 0, v_a_3281_);
                        v___x_3296_ = v___x_3288_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3297_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3281_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 1, v_b_3282_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3297_, 2, v_tail_3286_);
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
    mut v_a_3299_: *mut leanh::LeanObject,
    mut v_x_3300_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3301_: u8 = 0;
    let mut v_key_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3300_) == 0 {
                    v___x_3301_ = 0;
                    return v___x_3301_;
                } else {
                    v_key_3302_ = leanh::lean_ctor_get(v_x_3300_, 0);
                    v_tail_3303_ = leanh::lean_ctor_get(v_x_3300_, 2);
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
    mut v_a_3306_: *mut leanh::LeanObject,
    mut v_x_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3308_: u8 = 0;
    let mut v_r_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3308_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_3306_, v_x_3307_);
    leanh::lean_dec(v_x_3307_);
    leanh::lean_dec_ref(v_a_3306_);
    v_r_3309_ = leanh::lean_box((v_res_3308_) as usize);
    return v_r_3309_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(
    mut v_m_3310_: *mut leanh::LeanObject,
    mut v_a_3311_: *mut leanh::LeanObject,
    mut v_b_3312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: u8 = 0;
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut v_val_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3313_ = leanh::lean_ctor_get(v_m_3310_, 0);
                v_buckets_3314_ = leanh::lean_ctor_get(v_m_3310_, 1);
                v_isSharedCheck_3357_ = (!leanh::lean_is_exclusive(v_m_3310_)) as u8;
                if v_isSharedCheck_3357_ == 0 {
                    v___x_3316_ = v_m_3310_;
                    v_isShared_3317_ = v_isSharedCheck_3357_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3314_);
                    leanh::lean_inc(v_size_3313_);
                    leanh::lean_dec(v_m_3310_);
                    v___x_3316_ = leanh::lean_box(0);
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
                    v___x_3333_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3334_ = lean_nat_add(v_size_3313_, v___x_3333_);
                    leanh::lean_dec(v_size_3313_);
                    leanh::lean_inc(v_bkt_3331_);
                    v___x_3335_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3335_, 0, v_a_3311_);
                    leanh::lean_ctor_set(v___x_3335_, 1, v_b_3312_);
                    leanh::lean_ctor_set(v___x_3335_, 2, v_bkt_3331_);
                    v_buckets_x27_3336_ =
                        lean_array_uset(v_buckets_3314_, v___x_3330_, v___x_3335_);
                    v___x_3337_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3338_ = lean_nat_mul(v_size_x27_3334_, v___x_3337_);
                    v___x_3339_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3340_ = lean_nat_div(v___x_3338_, v___x_3339_);
                    leanh::lean_dec(v___x_3338_);
                    v___x_3341_ = lean_array_get_size(v_buckets_x27_3336_);
                    v___x_3342_ = lean_nat_dec_le(v___x_3340_, v___x_3341_);
                    leanh::lean_dec(v___x_3340_);
                    if v___x_3342_ == 0 {
                        v_val_3343_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_buckets_x27_3336_);
                        if v_isShared_3317_ == 0 {
                            leanh::lean_ctor_set(v___x_3316_, 1, v_val_3343_);
                            leanh::lean_ctor_set(v___x_3316_, 0, v_size_x27_3334_);
                            v___x_3345_ = v___x_3316_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3346_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3346_,
                                0,
                                v_size_x27_3334_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_val_3343_);
                            v___x_3345_ = v_reuseFailAlloc_3346_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3317_ == 0 {
                            leanh::lean_ctor_set(v___x_3316_, 1, v_buckets_x27_3336_);
                            leanh::lean_ctor_set(v___x_3316_, 0, v_size_x27_3334_);
                            v___x_3348_ = v___x_3316_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3349_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3349_,
                                0,
                                v_size_x27_3334_,
                            );
                            leanh::lean_ctor_set(
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
                    leanh::lean_inc(v_bkt_3331_);
                    v___x_3350_ = leanh::lean_box(0);
                    v_buckets_x27_3351_ =
                        lean_array_uset(v_buckets_3314_, v___x_3330_, v___x_3350_);
                    v___x_3352_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_3311_, v_b_3312_, v_bkt_3331_);
                    v___x_3353_ = lean_array_uset(v_buckets_x27_3351_, v___x_3330_, v___x_3352_);
                    if v_isShared_3317_ == 0 {
                        leanh::lean_ctor_set(v___x_3316_, 1, v___x_3353_);
                        v___x_3355_ = v___x_3316_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3356_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_size_3313_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3353_);
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
    mut v___x_3358_: *mut leanh::LeanObject,
    mut v___x_3359_: *mut leanh::LeanObject,
    mut v_fst_3360_: *mut leanh::LeanObject,
    mut v_fproof_3361_: *mut leanh::LeanObject,
    mut v_snd_3362_: *mut leanh::LeanObject,
    mut v_sproof_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v_val_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3384_: u8 = 0;
    let mut v_val_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_fproof_3361_) == 0 {
                    leanh::lean_dec_ref(v_snd_3362_);
                    leanh::lean_dec(v___x_3359_);
                    if leanh::lean_obj_tag(v_sproof_3363_) == 0 {
                        leanh::lean_dec_ref(v_fst_3360_);
                        leanh::lean_dec(v___x_3358_);
                        v___x_3364_ = leanh::lean_box(0);
                        return v___x_3364_;
                    } else {
                        v_val_3365_ = leanh::lean_ctor_get(v_sproof_3363_, 0);
                        v_isSharedCheck_3374_ =
                            (!leanh::lean_is_exclusive(v_sproof_3363_)) as u8;
                        if v_isSharedCheck_3374_ == 0 {
                            v___x_3367_ = v_sproof_3363_;
                            v_isShared_3368_ = v_isSharedCheck_3374_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3365_);
                            leanh::lean_dec(v_sproof_3363_);
                            v___x_3367_ = leanh::lean_box(0);
                            v_isShared_3368_ = v_isSharedCheck_3374_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fst_3360_);
                    leanh::lean_dec(v___x_3358_);
                    if leanh::lean_obj_tag(v_sproof_3363_) == 0 {
                        v_val_3375_ = leanh::lean_ctor_get(v_fproof_3361_, 0);
                        v_isSharedCheck_3384_ =
                            (!leanh::lean_is_exclusive(v_fproof_3361_)) as u8;
                        if v_isSharedCheck_3384_ == 0 {
                            v___x_3377_ = v_fproof_3361_;
                            v_isShared_3378_ = v_isSharedCheck_3384_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3375_);
                            leanh::lean_dec(v_fproof_3361_);
                            v___x_3377_ = leanh::lean_box(0);
                            v_isShared_3378_ = v_isSharedCheck_3384_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_snd_3362_);
                        leanh::lean_dec(v___x_3359_);
                        v_val_3385_ = leanh::lean_ctor_get(v_fproof_3361_, 0);
                        leanh::lean_inc(v_val_3385_);
                        leanh::lean_dec_ref_known(v_fproof_3361_, 1);
                        v_val_3386_ = leanh::lean_ctor_get(v_sproof_3363_, 0);
                        v_isSharedCheck_3394_ =
                            (!leanh::lean_is_exclusive(v_sproof_3363_)) as u8;
                        if v_isSharedCheck_3394_ == 0 {
                            v___x_3388_ = v_sproof_3363_;
                            v_isShared_3389_ = v_isSharedCheck_3394_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3386_);
                            leanh::lean_dec(v_sproof_3363_);
                            v___x_3388_ = leanh::lean_box(0);
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
                v___x_3370_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3370_, 0, v___x_3369_);
                leanh::lean_ctor_set(v___x_3370_, 1, v_val_3365_);
                if v_isShared_3368_ == 0 {
                    leanh::lean_ctor_set(v___x_3367_, 0, v___x_3370_);
                    v___x_3372_ = v___x_3367_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v___x_3370_);
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
                v___x_3380_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3380_, 0, v_val_3375_);
                leanh::lean_ctor_set(v___x_3380_, 1, v___x_3379_);
                if v_isShared_3378_ == 0 {
                    leanh::lean_ctor_set(v___x_3377_, 0, v___x_3380_);
                    v___x_3382_ = v___x_3377_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
                    v___x_3382_ = v_reuseFailAlloc_3383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3382_;
            }
            5 => {
                v___x_3390_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3390_, 0, v_val_3385_);
                leanh::lean_ctor_set(v___x_3390_, 1, v_val_3386_);
                if v_isShared_3389_ == 0 {
                    leanh::lean_ctor_set(v___x_3388_, 0, v___x_3390_);
                    v___x_3392_ = v___x_3388_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
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
    mut v_width_3397_: *mut leanh::LeanObject,
    mut v_expr_3398_: *mut leanh::LeanObject,
    mut v_width_3399_: *mut leanh::LeanObject,
    mut v_expr_3400_: *mut leanh::LeanObject,
    mut v_val_3401_: *mut leanh::LeanObject,
    mut v_val_3402_: *mut leanh::LeanObject,
    mut v___x_3403_: *mut leanh::LeanObject,
    mut v___x_3404_: *mut leanh::LeanObject,
    mut v___x_3405_: *mut leanh::LeanObject,
    mut v___x_3406_: *mut leanh::LeanObject,
    mut v___x_3407_: *mut leanh::LeanObject,
    mut v___x_3408_: *mut leanh::LeanObject,
    mut v___x_3409_: *mut leanh::LeanObject,
    mut v_arg_3410_: *mut leanh::LeanObject,
    mut v_arg_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
    mut v___y_3413_: *mut leanh::LeanObject,
    mut v___y_3414_: *mut leanh::LeanObject,
    mut v___y_3415_: *mut leanh::LeanObject,
    mut v___y_3416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3428_: u8 = 0;
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v_fst_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3452_: u8 = 0;
    let mut v_a_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3456_: u8 = 0;
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3460_: u8 = 0;
    let mut v_a_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3464_: u8 = 0;
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_width_3397_);
                v___x_3418_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                    v_width_3397_,
                    v_expr_3398_,
                    v___y_3412_,
                    v___y_3413_,
                    v___y_3414_,
                    v___y_3415_,
                    v___y_3416_,
                );
                if leanh::lean_obj_tag(v___x_3418_) == 0 {
                    v_a_3419_ = leanh::lean_ctor_get(v___x_3418_, 0);
                    leanh::lean_inc(v_a_3419_);
                    leanh::lean_dec_ref_known(v___x_3418_, 1);
                    leanh::lean_inc(v_width_3399_);
                    v___x_3420_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(
                        v_width_3399_,
                        v_expr_3400_,
                        v___y_3412_,
                        v___y_3413_,
                        v___y_3414_,
                        v___y_3415_,
                        v___y_3416_,
                    );
                    if leanh::lean_obj_tag(v___x_3420_) == 0 {
                        v_a_3421_ = leanh::lean_ctor_get(v___x_3420_, 0);
                        leanh::lean_inc(v_a_3421_);
                        leanh::lean_dec_ref_known(v___x_3420_, 1);
                        v___x_3422_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                            v_val_3401_,
                            v___y_3412_,
                            v___y_3413_,
                            v___y_3414_,
                            v___y_3415_,
                            v___y_3416_,
                        );
                        if leanh::lean_obj_tag(v___x_3422_) == 0 {
                            v_a_3423_ = leanh::lean_ctor_get(v___x_3422_, 0);
                            leanh::lean_inc(v_a_3423_);
                            leanh::lean_dec_ref_known(v___x_3422_, 1);
                            v___x_3424_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                                v_val_3402_,
                                v___y_3412_,
                                v___y_3413_,
                                v___y_3414_,
                                v___y_3415_,
                                v___y_3416_,
                            );
                            if leanh::lean_obj_tag(v___x_3424_) == 0 {
                                v_a_3425_ = leanh::lean_ctor_get(v___x_3424_, 0);
                                v_isSharedCheck_3452_ =
                                    (!leanh::lean_is_exclusive(v___x_3424_)) as u8;
                                if v_isSharedCheck_3452_ == 0 {
                                    v___x_3427_ = v___x_3424_;
                                    v_isShared_3428_ = v_isSharedCheck_3452_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3425_);
                                    leanh::lean_dec(v___x_3424_);
                                    v___x_3427_ = leanh::lean_box(0);
                                    v_isShared_3428_ = v_isSharedCheck_3452_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_3423_);
                                leanh::lean_dec(v_a_3421_);
                                leanh::lean_dec(v_a_3419_);
                                leanh::lean_dec_ref(v_arg_3411_);
                                leanh::lean_dec_ref(v_arg_3410_);
                                leanh::lean_dec_ref(v___x_3409_);
                                leanh::lean_dec_ref(v___x_3408_);
                                leanh::lean_dec(v___x_3407_);
                                leanh::lean_dec_ref(v___x_3406_);
                                leanh::lean_dec_ref(v___x_3405_);
                                leanh::lean_dec_ref(v___x_3404_);
                                leanh::lean_dec_ref(v___x_3403_);
                                leanh::lean_dec(v_width_3399_);
                                leanh::lean_dec(v_width_3397_);
                                return v___x_3424_;
                            }
                        } else {
                            leanh::lean_dec(v_a_3421_);
                            leanh::lean_dec(v_a_3419_);
                            leanh::lean_dec_ref(v_arg_3411_);
                            leanh::lean_dec_ref(v_arg_3410_);
                            leanh::lean_dec_ref(v___x_3409_);
                            leanh::lean_dec_ref(v___x_3408_);
                            leanh::lean_dec(v___x_3407_);
                            leanh::lean_dec_ref(v___x_3406_);
                            leanh::lean_dec_ref(v___x_3405_);
                            leanh::lean_dec_ref(v___x_3404_);
                            leanh::lean_dec_ref(v___x_3403_);
                            leanh::lean_dec_ref(v_val_3402_);
                            leanh::lean_dec(v_width_3399_);
                            leanh::lean_dec(v_width_3397_);
                            return v___x_3422_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3419_);
                        leanh::lean_dec_ref(v_arg_3411_);
                        leanh::lean_dec_ref(v_arg_3410_);
                        leanh::lean_dec_ref(v___x_3409_);
                        leanh::lean_dec_ref(v___x_3408_);
                        leanh::lean_dec(v___x_3407_);
                        leanh::lean_dec_ref(v___x_3406_);
                        leanh::lean_dec_ref(v___x_3405_);
                        leanh::lean_dec_ref(v___x_3404_);
                        leanh::lean_dec_ref(v___x_3403_);
                        leanh::lean_dec_ref(v_val_3402_);
                        leanh::lean_dec_ref(v_val_3401_);
                        leanh::lean_dec(v_width_3399_);
                        leanh::lean_dec(v_width_3397_);
                        v_a_3453_ = leanh::lean_ctor_get(v___x_3420_, 0);
                        v_isSharedCheck_3460_ =
                            (!leanh::lean_is_exclusive(v___x_3420_)) as u8;
                        if v_isSharedCheck_3460_ == 0 {
                            v___x_3455_ = v___x_3420_;
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3453_);
                            leanh::lean_dec(v___x_3420_);
                            v___x_3455_ = leanh::lean_box(0);
                            v_isShared_3456_ = v_isSharedCheck_3460_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_3411_);
                    leanh::lean_dec_ref(v_arg_3410_);
                    leanh::lean_dec_ref(v___x_3409_);
                    leanh::lean_dec_ref(v___x_3408_);
                    leanh::lean_dec(v___x_3407_);
                    leanh::lean_dec_ref(v___x_3406_);
                    leanh::lean_dec_ref(v___x_3405_);
                    leanh::lean_dec_ref(v___x_3404_);
                    leanh::lean_dec_ref(v___x_3403_);
                    leanh::lean_dec_ref(v_val_3402_);
                    leanh::lean_dec_ref(v_val_3401_);
                    leanh::lean_dec_ref(v_expr_3400_);
                    leanh::lean_dec(v_width_3399_);
                    leanh::lean_dec(v_width_3397_);
                    v_a_3461_ = leanh::lean_ctor_get(v___x_3418_, 0);
                    v_isSharedCheck_3468_ = (!leanh::lean_is_exclusive(v___x_3418_)) as u8;
                    if v_isSharedCheck_3468_ == 0 {
                        v___x_3463_ = v___x_3418_;
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3461_);
                        leanh::lean_dec(v___x_3418_);
                        v___x_3463_ = leanh::lean_box(0);
                        v_isShared_3464_ = v_isSharedCheck_3468_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_3421_);
                leanh::lean_inc(v_a_3419_);
                v___x_3429_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(v_width_3397_, v_width_3399_, v_a_3419_, v_a_3423_, v_a_3421_, v_a_3425_);
                if leanh::lean_obj_tag(v___x_3429_) == 1 {
                    v_val_3430_ = leanh::lean_ctor_get(v___x_3429_, 0);
                    v_isSharedCheck_3447_ = (!leanh::lean_is_exclusive(v___x_3429_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v___x_3432_ = v___x_3429_;
                        v_isShared_3433_ = v_isSharedCheck_3447_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3430_);
                        leanh::lean_dec(v___x_3429_);
                        v___x_3432_ = leanh::lean_box(0);
                        v_isShared_3433_ = v_isSharedCheck_3447_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3429_);
                    leanh::lean_dec(v_a_3421_);
                    leanh::lean_dec(v_a_3419_);
                    leanh::lean_dec_ref(v_arg_3411_);
                    leanh::lean_dec_ref(v_arg_3410_);
                    leanh::lean_dec_ref(v___x_3409_);
                    leanh::lean_dec_ref(v___x_3408_);
                    leanh::lean_dec(v___x_3407_);
                    leanh::lean_dec_ref(v___x_3406_);
                    leanh::lean_dec_ref(v___x_3405_);
                    leanh::lean_dec_ref(v___x_3404_);
                    leanh::lean_dec_ref(v___x_3403_);
                    v___x_3448_ = leanh::lean_box(0);
                    if v_isShared_3428_ == 0 {
                        leanh::lean_ctor_set(v___x_3427_, 0, v___x_3448_);
                        v___x_3450_ = v___x_3427_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
                        v___x_3450_ = v_reuseFailAlloc_3451_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3434_ = leanh::lean_ctor_get(v_val_3430_, 0);
                leanh::lean_inc(v_fst_3434_);
                v_snd_3435_ = leanh::lean_ctor_get(v_val_3430_, 1);
                leanh::lean_inc(v_snd_3435_);
                leanh::lean_dec(v_val_3430_);
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
                    leanh::lean_ctor_set(v___x_3432_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3432_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3440_);
                    v___x_3442_ = v_reuseFailAlloc_3446_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3428_ == 0 {
                    leanh::lean_ctor_set(v___x_3427_, 0, v___x_3442_);
                    v___x_3444_ = v___x_3427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
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
                    v_reuseFailAlloc_3459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
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
                    v_reuseFailAlloc_3467_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_width_3469_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_expr_3470_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_width_3471_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_expr_3472_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_val_3473_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_val_3474_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_3475_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_3476_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_3477_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_3478_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_3479_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_3480_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_3481_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_arg_3482_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_arg_3483_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3484_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3485_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_3486_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_3487_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_3488_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_3489_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_res_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3490_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0(v_width_3469_, v_expr_3470_, v_width_3471_, v_expr_3472_, v_val_3473_, v_val_3474_, v___x_3475_, v___x_3476_, v___x_3477_, v___x_3478_, v___x_3479_, v___x_3480_, v___x_3481_, v_arg_3482_, v_arg_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
    leanh::lean_dec(v___y_3488_);
    leanh::lean_dec_ref(v___y_3487_);
    leanh::lean_dec(v___y_3486_);
    leanh::lean_dec_ref(v___y_3485_);
    leanh::lean_dec(v___y_3484_);
    return v_res_3490_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(
    mut v_n_3491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3492_, 0, v_n_3491_);
    return v___x_3492_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(
    mut v_n_3493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3494_, 0, v_n_3493_);
    return v___x_3494_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(
    mut v_msgData_3495_: *mut leanh::LeanObject,
    mut v___y_3496_: *mut leanh::LeanObject,
    mut v___y_3497_: *mut leanh::LeanObject,
    mut v___y_3498_: *mut leanh::LeanObject,
    mut v___y_3499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3501_ = lean_st_ref_get(v___y_3499_);
    v_env_3502_ = leanh::lean_ctor_get(v___x_3501_, 0);
    leanh::lean_inc_ref(v_env_3502_);
    leanh::lean_dec(v___x_3501_);
    v___x_3503_ = lean_st_ref_get(v___y_3497_);
    v_mctx_3504_ = leanh::lean_ctor_get(v___x_3503_, 0);
    leanh::lean_inc_ref(v_mctx_3504_);
    leanh::lean_dec(v___x_3503_);
    v_lctx_3505_ = leanh::lean_ctor_get(v___y_3496_, 2);
    v_options_3506_ = leanh::lean_ctor_get(v___y_3498_, 2);
    leanh::lean_inc_ref(v_options_3506_);
    leanh::lean_inc_ref(v_lctx_3505_);
    v___x_3507_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3507_, 0, v_env_3502_);
    leanh::lean_ctor_set(v___x_3507_, 1, v_mctx_3504_);
    leanh::lean_ctor_set(v___x_3507_, 2, v_lctx_3505_);
    leanh::lean_ctor_set(v___x_3507_, 3, v_options_3506_);
    v___x_3508_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3508_, 0, v___x_3507_);
    leanh::lean_ctor_set(v___x_3508_, 1, v_msgData_3495_);
    v___x_3509_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3509_, 0, v___x_3508_);
    return v___x_3509_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(
    mut v_msgData_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
    mut v___y_3513_: *mut leanh::LeanObject,
    mut v___y_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3516_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(v_msgData_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
    leanh::lean_dec(v___y_3514_);
    leanh::lean_dec_ref(v___y_3513_);
    leanh::lean_dec(v___y_3512_);
    leanh::lean_dec_ref(v___y_3511_);
    return v_res_3516_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(
    mut v_msg_3517_: *mut leanh::LeanObject,
    mut v___y_3518_: *mut leanh::LeanObject,
    mut v___y_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
    mut v___y_3521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3523_ = leanh::lean_ctor_get(v___y_3520_, 5);
                v___x_3524_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(v_msg_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
                v_a_3525_ = leanh::lean_ctor_get(v___x_3524_, 0);
                v_isSharedCheck_3533_ = (!leanh::lean_is_exclusive(v___x_3524_)) as u8;
                if v_isSharedCheck_3533_ == 0 {
                    v___x_3527_ = v___x_3524_;
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3525_);
                    leanh::lean_dec(v___x_3524_);
                    v___x_3527_ = leanh::lean_box(0);
                    v_isShared_3528_ = v_isSharedCheck_3533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3523_);
                v___x_3529_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3529_, 0, v_ref_3523_);
                leanh::lean_ctor_set(v___x_3529_, 1, v_a_3525_);
                if v_isShared_3528_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3527_, 1);
                    leanh::lean_ctor_set(v___x_3527_, 0, v___x_3529_);
                    v___x_3531_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
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
    mut v_msg_3534_: *mut leanh::LeanObject,
    mut v___y_3535_: *mut leanh::LeanObject,
    mut v___y_3536_: *mut leanh::LeanObject,
    mut v___y_3537_: *mut leanh::LeanObject,
    mut v___y_3538_: *mut leanh::LeanObject,
    mut v___y_3539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3540_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
    leanh::lean_dec(v___y_3538_);
    leanh::lean_dec_ref(v___y_3537_);
    leanh::lean_dec(v___y_3536_);
    leanh::lean_dec_ref(v___y_3535_);
    return v_res_3540_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(
    mut v_width_3542_: *mut leanh::LeanObject,
    mut v_expr_3543_: *mut leanh::LeanObject,
    mut v_val_3544_: *mut leanh::LeanObject,
    mut v___x_3545_: *mut leanh::LeanObject,
    mut v___x_3546_: *mut leanh::LeanObject,
    mut v___x_3547_: *mut leanh::LeanObject,
    mut v___x_3548_: *mut leanh::LeanObject,
    mut v___x_3549_: *mut leanh::LeanObject,
    mut v___x_3550_: *mut leanh::LeanObject,
    mut v___x_3551_: *mut leanh::LeanObject,
    mut v_arg_3552_: *mut leanh::LeanObject,
    mut v___y_3553_: *mut leanh::LeanObject,
    mut v___y_3554_: *mut leanh::LeanObject,
    mut v___y_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3565_: u8 = 0;
    let mut v_val_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut v_a_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_3559_) == 0 {
                    v_a_3560_ = leanh::lean_ctor_get(v___x_3559_, 0);
                    leanh::lean_inc(v_a_3560_);
                    leanh::lean_dec_ref_known(v___x_3559_, 1);
                    v___x_3561_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                        v_val_3544_,
                        v___y_3553_,
                        v___y_3554_,
                        v___y_3555_,
                        v___y_3556_,
                        v___y_3557_,
                    );
                    if leanh::lean_obj_tag(v___x_3561_) == 0 {
                        v_a_3562_ = leanh::lean_ctor_get(v___x_3561_, 0);
                        v_isSharedCheck_3586_ =
                            (!leanh::lean_is_exclusive(v___x_3561_)) as u8;
                        if v_isSharedCheck_3586_ == 0 {
                            v___x_3564_ = v___x_3561_;
                            v_isShared_3565_ = v_isSharedCheck_3586_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3562_);
                            leanh::lean_dec(v___x_3561_);
                            v___x_3564_ = leanh::lean_box(0);
                            v_isShared_3565_ = v_isSharedCheck_3586_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3560_);
                        leanh::lean_dec_ref(v_arg_3552_);
                        leanh::lean_dec_ref(v___x_3551_);
                        leanh::lean_dec_ref(v___x_3550_);
                        leanh::lean_dec(v___x_3549_);
                        leanh::lean_dec_ref(v___x_3548_);
                        leanh::lean_dec_ref(v___x_3547_);
                        leanh::lean_dec_ref(v___x_3546_);
                        leanh::lean_dec_ref(v___x_3545_);
                        return v___x_3561_;
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_3552_);
                    leanh::lean_dec_ref(v___x_3551_);
                    leanh::lean_dec_ref(v___x_3550_);
                    leanh::lean_dec(v___x_3549_);
                    leanh::lean_dec_ref(v___x_3548_);
                    leanh::lean_dec_ref(v___x_3547_);
                    leanh::lean_dec_ref(v___x_3546_);
                    leanh::lean_dec_ref(v___x_3545_);
                    leanh::lean_dec_ref(v_val_3544_);
                    v_a_3587_ = leanh::lean_ctor_get(v___x_3559_, 0);
                    v_isSharedCheck_3594_ = (!leanh::lean_is_exclusive(v___x_3559_)) as u8;
                    if v_isSharedCheck_3594_ == 0 {
                        v___x_3589_ = v___x_3559_;
                        v_isShared_3590_ = v_isSharedCheck_3594_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3587_);
                        leanh::lean_dec(v___x_3559_);
                        v___x_3589_ = leanh::lean_box(0);
                        v_isShared_3590_ = v_isSharedCheck_3594_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3562_) == 1 {
                    v_val_3566_ = leanh::lean_ctor_get(v_a_3562_, 0);
                    v_isSharedCheck_3581_ = (!leanh::lean_is_exclusive(v_a_3562_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3568_ = v_a_3562_;
                        v_isShared_3569_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3566_);
                        leanh::lean_dec(v_a_3562_);
                        v___x_3568_ = leanh::lean_box(0);
                        v_isShared_3569_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3562_);
                    leanh::lean_dec(v_a_3560_);
                    leanh::lean_dec_ref(v_arg_3552_);
                    leanh::lean_dec_ref(v___x_3551_);
                    leanh::lean_dec_ref(v___x_3550_);
                    leanh::lean_dec(v___x_3549_);
                    leanh::lean_dec_ref(v___x_3548_);
                    leanh::lean_dec_ref(v___x_3547_);
                    leanh::lean_dec_ref(v___x_3546_);
                    leanh::lean_dec_ref(v___x_3545_);
                    v___x_3582_ = leanh::lean_box(0);
                    if v_isShared_3565_ == 0 {
                        leanh::lean_ctor_set(v___x_3564_, 0, v___x_3582_);
                        v___x_3584_ = v___x_3564_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3585_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
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
                    leanh::lean_ctor_set(v___x_3568_, 0, v___x_3574_);
                    v___x_3576_ = v___x_3568_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3574_);
                    v___x_3576_ = v_reuseFailAlloc_3580_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3565_ == 0 {
                    leanh::lean_ctor_set(v___x_3564_, 0, v___x_3576_);
                    v___x_3578_ = v___x_3564_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
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
                    v_reuseFailAlloc_3593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_width_3595_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_expr_3596_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_val_3597_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_3598_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_3599_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_3600_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_3601_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_3602_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_3603_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_3604_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_arg_3605_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_3606_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_3607_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_3608_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3609_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3610_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3611_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3612_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(v_width_3595_, v_expr_3596_, v_val_3597_, v___x_3598_, v___x_3599_, v___x_3600_, v___x_3601_, v___x_3602_, v___x_3603_, v___x_3604_, v_arg_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
    leanh::lean_dec(v___y_3610_);
    leanh::lean_dec_ref(v___y_3609_);
    leanh::lean_dec(v___y_3608_);
    leanh::lean_dec_ref(v___y_3607_);
    leanh::lean_dec(v___y_3606_);
    return v_res_3612_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(
    mut v_width_3614_: *mut leanh::LeanObject,
    mut v_expr_3615_: *mut leanh::LeanObject,
    mut v_val_3616_: *mut leanh::LeanObject,
    mut v___x_3617_: *mut leanh::LeanObject,
    mut v___x_3618_: *mut leanh::LeanObject,
    mut v___x_3619_: *mut leanh::LeanObject,
    mut v___x_3620_: *mut leanh::LeanObject,
    mut v___x_3621_: *mut leanh::LeanObject,
    mut v_arg_3622_: *mut leanh::LeanObject,
    mut v_arg_3623_: *mut leanh::LeanObject,
    mut v___x_3624_: *mut leanh::LeanObject,
    mut v_arg_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
    mut v___y_3627_: *mut leanh::LeanObject,
    mut v___y_3628_: *mut leanh::LeanObject,
    mut v___y_3629_: *mut leanh::LeanObject,
    mut v___y_3630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v_val_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3642_: u8 = 0;
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3654_: u8 = 0;
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v_a_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_3632_) == 0 {
                    v_a_3633_ = leanh::lean_ctor_get(v___x_3632_, 0);
                    leanh::lean_inc(v_a_3633_);
                    leanh::lean_dec_ref_known(v___x_3632_, 1);
                    v___x_3634_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(
                        v_val_3616_,
                        v___y_3626_,
                        v___y_3627_,
                        v___y_3628_,
                        v___y_3629_,
                        v___y_3630_,
                    );
                    if leanh::lean_obj_tag(v___x_3634_) == 0 {
                        v_a_3635_ = leanh::lean_ctor_get(v___x_3634_, 0);
                        v_isSharedCheck_3659_ =
                            (!leanh::lean_is_exclusive(v___x_3634_)) as u8;
                        if v_isSharedCheck_3659_ == 0 {
                            v___x_3637_ = v___x_3634_;
                            v_isShared_3638_ = v_isSharedCheck_3659_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3635_);
                            leanh::lean_dec(v___x_3634_);
                            v___x_3637_ = leanh::lean_box(0);
                            v_isShared_3638_ = v_isSharedCheck_3659_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3633_);
                        leanh::lean_dec_ref(v_arg_3625_);
                        leanh::lean_dec_ref(v___x_3624_);
                        leanh::lean_dec_ref(v_arg_3623_);
                        leanh::lean_dec_ref(v_arg_3622_);
                        leanh::lean_dec(v___x_3621_);
                        leanh::lean_dec_ref(v___x_3620_);
                        leanh::lean_dec_ref(v___x_3619_);
                        leanh::lean_dec_ref(v___x_3618_);
                        leanh::lean_dec_ref(v___x_3617_);
                        return v___x_3634_;
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_3625_);
                    leanh::lean_dec_ref(v___x_3624_);
                    leanh::lean_dec_ref(v_arg_3623_);
                    leanh::lean_dec_ref(v_arg_3622_);
                    leanh::lean_dec(v___x_3621_);
                    leanh::lean_dec_ref(v___x_3620_);
                    leanh::lean_dec_ref(v___x_3619_);
                    leanh::lean_dec_ref(v___x_3618_);
                    leanh::lean_dec_ref(v___x_3617_);
                    leanh::lean_dec_ref(v_val_3616_);
                    v_a_3660_ = leanh::lean_ctor_get(v___x_3632_, 0);
                    v_isSharedCheck_3667_ = (!leanh::lean_is_exclusive(v___x_3632_)) as u8;
                    if v_isSharedCheck_3667_ == 0 {
                        v___x_3662_ = v___x_3632_;
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3660_);
                        leanh::lean_dec(v___x_3632_);
                        v___x_3662_ = leanh::lean_box(0);
                        v_isShared_3663_ = v_isSharedCheck_3667_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3635_) == 1 {
                    v_val_3639_ = leanh::lean_ctor_get(v_a_3635_, 0);
                    v_isSharedCheck_3654_ = (!leanh::lean_is_exclusive(v_a_3635_)) as u8;
                    if v_isSharedCheck_3654_ == 0 {
                        v___x_3641_ = v_a_3635_;
                        v_isShared_3642_ = v_isSharedCheck_3654_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3639_);
                        leanh::lean_dec(v_a_3635_);
                        v___x_3641_ = leanh::lean_box(0);
                        v_isShared_3642_ = v_isSharedCheck_3654_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3635_);
                    leanh::lean_dec(v_a_3633_);
                    leanh::lean_dec_ref(v_arg_3625_);
                    leanh::lean_dec_ref(v___x_3624_);
                    leanh::lean_dec_ref(v_arg_3623_);
                    leanh::lean_dec_ref(v_arg_3622_);
                    leanh::lean_dec(v___x_3621_);
                    leanh::lean_dec_ref(v___x_3620_);
                    leanh::lean_dec_ref(v___x_3619_);
                    leanh::lean_dec_ref(v___x_3618_);
                    leanh::lean_dec_ref(v___x_3617_);
                    v___x_3655_ = leanh::lean_box(0);
                    if v_isShared_3638_ == 0 {
                        leanh::lean_ctor_set(v___x_3637_, 0, v___x_3655_);
                        v___x_3657_ = v___x_3637_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3658_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
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
                    leanh::lean_ctor_set(v___x_3641_, 0, v___x_3647_);
                    v___x_3649_ = v___x_3641_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3647_);
                    v___x_3649_ = v_reuseFailAlloc_3653_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3638_ == 0 {
                    leanh::lean_ctor_set(v___x_3637_, 0, v___x_3649_);
                    v___x_3651_ = v___x_3637_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
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
                    v_reuseFailAlloc_3666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_width_3668_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_expr_3669_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_val_3670_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_3671_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_3672_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_3673_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_3674_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_3675_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_arg_3676_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_arg_3677_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_3678_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_arg_3679_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_3680_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_3681_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3682_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3683_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3684_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_3685_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3686_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(v_width_3668_, v_expr_3669_, v_val_3670_, v___x_3671_, v___x_3672_, v___x_3673_, v___x_3674_, v___x_3675_, v_arg_3676_, v_arg_3677_, v___x_3678_, v_arg_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
    leanh::lean_dec(v___y_3684_);
    leanh::lean_dec_ref(v___y_3683_);
    leanh::lean_dec(v___y_3682_);
    leanh::lean_dec_ref(v___y_3681_);
    leanh::lean_dec(v___y_3680_);
    return v_res_3686_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2(
    mut v_n_3687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3688_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3688_, 0, v_n_3687_);
    return v___x_3688_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ = leanh::lean_box(0);
    v___x_3804_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1;
    v___x_3805_ = l_Lean_mkConst(v___x_3804_, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3814_ = leanh::lean_box(0);
    v___x_3815_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5;
    v___x_3816_ = l_Lean_mkConst(v___x_3815_, v___x_3814_);
    return v___x_3816_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3824_ = leanh::lean_box(0);
    v___x_3825_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8;
    v___x_3826_ = l_Lean_mkConst(v___x_3825_, v___x_3824_);
    return v___x_3826_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3834_ = leanh::lean_box(0);
    v___x_3835_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11;
    v___x_3836_ = l_Lean_mkConst(v___x_3835_, v___x_3834_);
    return v___x_3836_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3844_ = leanh::lean_box(0);
    v___x_3845_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14;
    v___x_3846_ = l_Lean_mkConst(v___x_3845_, v___x_3844_);
    return v___x_3846_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3854_ = leanh::lean_box(0);
    v___x_3855_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17;
    v___x_3856_ = l_Lean_mkConst(v___x_3855_, v___x_3854_);
    return v___x_3856_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = leanh::lean_box(0);
    v___x_3865_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20;
    v___x_3866_ = l_Lean_mkConst(v___x_3865_, v___x_3864_);
    return v___x_3866_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = leanh::lean_box(0);
    v___x_3875_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23;
    v___x_3876_ = l_Lean_mkConst(v___x_3875_, v___x_3874_);
    return v___x_3876_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(
    mut v_lhsExpr_3877_: *mut leanh::LeanObject,
    mut v_rhsExpr_3878_: *mut leanh::LeanObject,
    mut v_op_3879_: u8,
    mut v_congrThm_3880_: *mut leanh::LeanObject,
    mut v_origExpr_3881_: *mut leanh::LeanObject,
    mut v_a_3882_: *mut leanh::LeanObject,
    mut v_a_3883_: *mut leanh::LeanObject,
    mut v_a_3884_: *mut leanh::LeanObject,
    mut v_a_3885_: *mut leanh::LeanObject,
    mut v_a_3886_: *mut leanh::LeanObject,
    mut v_a_3887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3893_: u8 = 0;
    let mut v_val_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v_val_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3903_: u8 = 0;
    let mut v_width_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: u8 = 0;
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3939_: u8 = 0;
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_lhsExpr_3877_);
                v___x_3889_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_lhsExpr_3877_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
                if leanh::lean_obj_tag(v___x_3889_) == 0 {
                    v_a_3890_ = leanh::lean_ctor_get(v___x_3889_, 0);
                    v_isSharedCheck_3949_ = (!leanh::lean_is_exclusive(v___x_3889_)) as u8;
                    if v_isSharedCheck_3949_ == 0 {
                        v___x_3892_ = v___x_3889_;
                        v_isShared_3893_ = v_isSharedCheck_3949_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3890_);
                        leanh::lean_dec(v___x_3889_);
                        v___x_3892_ = leanh::lean_box(0);
                        v_isShared_3893_ = v_isSharedCheck_3949_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_3881_);
                    leanh::lean_dec(v_congrThm_3880_);
                    leanh::lean_dec_ref(v_rhsExpr_3878_);
                    leanh::lean_dec_ref(v_lhsExpr_3877_);
                    return v___x_3889_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3890_) == 1 {
                    leanh::lean_del_object(v___x_3892_);
                    v_val_3894_ = leanh::lean_ctor_get(v_a_3890_, 0);
                    leanh::lean_inc(v_val_3894_);
                    leanh::lean_dec_ref_known(v_a_3890_, 1);
                    leanh::lean_inc_ref(v_rhsExpr_3878_);
                    v___x_3895_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_rhsExpr_3878_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_);
                    if leanh::lean_obj_tag(v___x_3895_) == 0 {
                        v_a_3896_ = leanh::lean_ctor_get(v___x_3895_, 0);
                        v_isSharedCheck_3944_ =
                            (!leanh::lean_is_exclusive(v___x_3895_)) as u8;
                        if v_isSharedCheck_3944_ == 0 {
                            v___x_3898_ = v___x_3895_;
                            v_isShared_3899_ = v_isSharedCheck_3944_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3896_);
                            leanh::lean_dec(v___x_3895_);
                            v___x_3898_ = leanh::lean_box(0);
                            v_isShared_3899_ = v_isSharedCheck_3944_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_3894_);
                        leanh::lean_dec_ref(v_origExpr_3881_);
                        leanh::lean_dec(v_congrThm_3880_);
                        leanh::lean_dec_ref(v_rhsExpr_3878_);
                        leanh::lean_dec_ref(v_lhsExpr_3877_);
                        return v___x_3895_;
                    }
                } else {
                    leanh::lean_dec(v_a_3890_);
                    leanh::lean_dec_ref(v_origExpr_3881_);
                    leanh::lean_dec(v_congrThm_3880_);
                    leanh::lean_dec_ref(v_rhsExpr_3878_);
                    leanh::lean_dec_ref(v_lhsExpr_3877_);
                    v___x_3945_ = leanh::lean_box(0);
                    if v_isShared_3893_ == 0 {
                        leanh::lean_ctor_set(v___x_3892_, 0, v___x_3945_);
                        v___x_3947_ = v___x_3892_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3948_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
                        v___x_3947_ = v_reuseFailAlloc_3948_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3896_) == 1 {
                    v_val_3900_ = leanh::lean_ctor_get(v_a_3896_, 0);
                    v_isSharedCheck_3939_ = (!leanh::lean_is_exclusive(v_a_3896_)) as u8;
                    if v_isSharedCheck_3939_ == 0 {
                        v___x_3902_ = v_a_3896_;
                        v_isShared_3903_ = v_isSharedCheck_3939_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3900_);
                        leanh::lean_dec(v_a_3896_);
                        v___x_3902_ = leanh::lean_box(0);
                        v_isShared_3903_ = v_isSharedCheck_3939_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3896_);
                    leanh::lean_dec(v_val_3894_);
                    leanh::lean_dec_ref(v_origExpr_3881_);
                    leanh::lean_dec(v_congrThm_3880_);
                    leanh::lean_dec_ref(v_rhsExpr_3878_);
                    leanh::lean_dec_ref(v_lhsExpr_3877_);
                    v___x_3940_ = leanh::lean_box(0);
                    if v_isShared_3899_ == 0 {
                        leanh::lean_ctor_set(v___x_3898_, 0, v___x_3940_);
                        v___x_3942_ = v___x_3898_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
                        v___x_3942_ = v_reuseFailAlloc_3943_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_width_3904_ = leanh::lean_ctor_get(v_val_3900_, 0);
                v_bvExpr_3905_ = leanh::lean_ctor_get(v_val_3900_, 1);
                v_expr_3906_ = leanh::lean_ctor_get(v_val_3900_, 4);
                v_width_3907_ = leanh::lean_ctor_get(v_val_3894_, 0);
                leanh::lean_inc(v_width_3907_);
                v_bvExpr_3908_ = leanh::lean_ctor_get(v_val_3894_, 1);
                v_expr_3909_ = leanh::lean_ctor_get(v_val_3894_, 4);
                v___x_3910_ = lean_nat_dec_eq(v_width_3904_, v_width_3907_);
                if v___x_3910_ == 0 {
                    leanh::lean_dec(v_width_3907_);
                    leanh::lean_del_object(v___x_3902_);
                    leanh::lean_dec(v_val_3900_);
                    leanh::lean_dec(v_val_3894_);
                    leanh::lean_dec_ref(v_origExpr_3881_);
                    leanh::lean_dec(v_congrThm_3880_);
                    leanh::lean_dec_ref(v_rhsExpr_3878_);
                    leanh::lean_dec_ref(v_lhsExpr_3877_);
                    v___x_3911_ = leanh::lean_box(0);
                    if v_isShared_3899_ == 0 {
                        leanh::lean_ctor_set(v___x_3898_, 0, v___x_3911_);
                        v___x_3913_ = v___x_3898_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
                        v___x_3913_ = v_reuseFailAlloc_3914_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_bvExpr_3905_);
                    leanh::lean_inc_ref(v_bvExpr_3908_);
                    leanh::lean_inc_n(v_width_3907_, 2);
                    v___x_3915_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(
                        v_width_3907_,
                        v_bvExpr_3908_,
                        v_op_3879_,
                        v_bvExpr_3905_,
                    );
                    v___x_3916_ = leanh::lean_box(0);
                    v___x_3917_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2);
                    v___x_3918_ = l_Lean_mkNatLit(v_width_3907_);
                    match v_op_3879_ {
                        0 => {
                            v___x_3932_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6);
                            v___y_3920_ = v___x_3932_;
                            state = 5;
                            continue;
                        }
                        1 => {
                            v___x_3933_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9);
                            v___y_3920_ = v___x_3933_;
                            state = 5;
                            continue;
                        }
                        2 => {
                            v___x_3934_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12);
                            v___y_3920_ = v___x_3934_;
                            state = 5;
                            continue;
                        }
                        3 => {
                            v___x_3935_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15);
                            v___y_3920_ = v___x_3935_;
                            state = 5;
                            continue;
                        }
                        4 => {
                            v___x_3936_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18);
                            v___y_3920_ = v___x_3936_;
                            state = 5;
                            continue;
                        }
                        5 => {
                            v___x_3937_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21);
                            v___y_3920_ = v___x_3937_;
                            state = 5;
                            continue;
                        }
                        _ => {
                            v___x_3938_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24);
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
                leanh::lean_inc_ref(v_expr_3906_);
                leanh::lean_inc_ref(v___y_3920_);
                leanh::lean_inc_ref(v_expr_3909_);
                leanh::lean_inc_ref(v___x_3918_);
                v___x_3921_ = l_Lean_mkApp4(
                    v___x_3917_,
                    v___x_3918_,
                    v_expr_3909_,
                    v___y_3920_,
                    v_expr_3906_,
                );
                v___x_3922_ = l_Lean_mkConst(v_congrThm_3880_, v___x_3916_);
                v___x_3923_ = l_Lean_Expr_app___override(v___x_3922_, v___x_3918_);
                v___x_3924_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed as *mut core::ffi::c_void, 11, 5);
                leanh::lean_closure_set(v___x_3924_, 0, v_val_3894_);
                leanh::lean_closure_set(v___x_3924_, 1, v_val_3900_);
                leanh::lean_closure_set(v___x_3924_, 2, v_lhsExpr_3877_);
                leanh::lean_closure_set(v___x_3924_, 3, v_rhsExpr_3878_);
                leanh::lean_closure_set(v___x_3924_, 4, v___x_3923_);
                v___x_3925_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3925_, 0, v_width_3907_);
                leanh::lean_ctor_set(v___x_3925_, 1, v___x_3915_);
                leanh::lean_ctor_set(v___x_3925_, 2, v_origExpr_3881_);
                leanh::lean_ctor_set(v___x_3925_, 3, v___x_3924_);
                leanh::lean_ctor_set(v___x_3925_, 4, v___x_3921_);
                if v_isShared_3903_ == 0 {
                    leanh::lean_ctor_set(v___x_3902_, 0, v___x_3925_);
                    v___x_3927_ = v___x_3902_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3925_);
                    v___x_3927_ = v_reuseFailAlloc_3931_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3899_ == 0 {
                    leanh::lean_ctor_set(v___x_3898_, 0, v___x_3927_);
                    v___x_3929_ = v___x_3898_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
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
    mut v_distanceExpr_4008_: *mut leanh::LeanObject,
    mut v_innerExpr_4009_: *mut leanh::LeanObject,
    mut v_shiftOp_4010_: *mut leanh::LeanObject,
    mut v_shiftOpName_4011_: *mut leanh::LeanObject,
    mut v_congrThm_4012_: *mut leanh::LeanObject,
    mut v_origExpr_4013_: *mut leanh::LeanObject,
    mut v_a_4014_: *mut leanh::LeanObject,
    mut v_a_4015_: *mut leanh::LeanObject,
    mut v_a_4016_: *mut leanh::LeanObject,
    mut v_a_4017_: *mut leanh::LeanObject,
    mut v_a_4018_: *mut leanh::LeanObject,
    mut v_a_4019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4025_: u8 = 0;
    let mut v_val_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v_val_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v_width_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_innerExpr_4009_);
                v___x_4021_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4009_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
                if leanh::lean_obj_tag(v___x_4021_) == 0 {
                    v_a_4022_ = leanh::lean_ctor_get(v___x_4021_, 0);
                    v_isSharedCheck_4068_ = (!leanh::lean_is_exclusive(v___x_4021_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v___x_4024_ = v___x_4021_;
                        v_isShared_4025_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4022_);
                        leanh::lean_dec(v___x_4021_);
                        v___x_4024_ = leanh::lean_box(0);
                        v_isShared_4025_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4013_);
                    leanh::lean_dec(v_congrThm_4012_);
                    leanh::lean_dec(v_shiftOpName_4011_);
                    leanh::lean_dec_ref(v_shiftOp_4010_);
                    leanh::lean_dec_ref(v_innerExpr_4009_);
                    leanh::lean_dec_ref(v_distanceExpr_4008_);
                    return v___x_4021_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4022_) == 1 {
                    leanh::lean_del_object(v___x_4024_);
                    v_val_4026_ = leanh::lean_ctor_get(v_a_4022_, 0);
                    leanh::lean_inc(v_val_4026_);
                    leanh::lean_dec_ref_known(v_a_4022_, 1);
                    leanh::lean_inc_ref(v_distanceExpr_4008_);
                    v___x_4027_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_distanceExpr_4008_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
                    if leanh::lean_obj_tag(v___x_4027_) == 0 {
                        v_a_4028_ = leanh::lean_ctor_get(v___x_4027_, 0);
                        v_isSharedCheck_4063_ =
                            (!leanh::lean_is_exclusive(v___x_4027_)) as u8;
                        if v_isSharedCheck_4063_ == 0 {
                            v___x_4030_ = v___x_4027_;
                            v_isShared_4031_ = v_isSharedCheck_4063_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4028_);
                            leanh::lean_dec(v___x_4027_);
                            v___x_4030_ = leanh::lean_box(0);
                            v_isShared_4031_ = v_isSharedCheck_4063_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4026_);
                        leanh::lean_dec_ref(v_origExpr_4013_);
                        leanh::lean_dec(v_congrThm_4012_);
                        leanh::lean_dec(v_shiftOpName_4011_);
                        leanh::lean_dec_ref(v_shiftOp_4010_);
                        leanh::lean_dec_ref(v_innerExpr_4009_);
                        leanh::lean_dec_ref(v_distanceExpr_4008_);
                        return v___x_4027_;
                    }
                } else {
                    leanh::lean_dec(v_a_4022_);
                    leanh::lean_dec_ref(v_origExpr_4013_);
                    leanh::lean_dec(v_congrThm_4012_);
                    leanh::lean_dec(v_shiftOpName_4011_);
                    leanh::lean_dec_ref(v_shiftOp_4010_);
                    leanh::lean_dec_ref(v_innerExpr_4009_);
                    leanh::lean_dec_ref(v_distanceExpr_4008_);
                    v___x_4064_ = leanh::lean_box(0);
                    if v_isShared_4025_ == 0 {
                        leanh::lean_ctor_set(v___x_4024_, 0, v___x_4064_);
                        v___x_4066_ = v___x_4024_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4067_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
                        v___x_4066_ = v_reuseFailAlloc_4067_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4028_) == 1 {
                    v_val_4032_ = leanh::lean_ctor_get(v_a_4028_, 0);
                    v_isSharedCheck_4058_ = (!leanh::lean_is_exclusive(v_a_4028_)) as u8;
                    if v_isSharedCheck_4058_ == 0 {
                        v___x_4034_ = v_a_4028_;
                        v_isShared_4035_ = v_isSharedCheck_4058_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4032_);
                        leanh::lean_dec(v_a_4028_);
                        v___x_4034_ = leanh::lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4058_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4028_);
                    leanh::lean_dec(v_val_4026_);
                    leanh::lean_dec_ref(v_origExpr_4013_);
                    leanh::lean_dec(v_congrThm_4012_);
                    leanh::lean_dec(v_shiftOpName_4011_);
                    leanh::lean_dec_ref(v_shiftOp_4010_);
                    leanh::lean_dec_ref(v_innerExpr_4009_);
                    leanh::lean_dec_ref(v_distanceExpr_4008_);
                    v___x_4059_ = leanh::lean_box(0);
                    if v_isShared_4031_ == 0 {
                        leanh::lean_ctor_set(v___x_4030_, 0, v___x_4059_);
                        v___x_4061_ = v___x_4030_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
                        v___x_4061_ = v_reuseFailAlloc_4062_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_width_4036_ = leanh::lean_ctor_get(v_val_4026_, 0);
                leanh::lean_inc_n(v_width_4036_, 3);
                v_bvExpr_4037_ = leanh::lean_ctor_get(v_val_4026_, 1);
                v_expr_4038_ = leanh::lean_ctor_get(v_val_4026_, 4);
                v_width_4039_ = leanh::lean_ctor_get(v_val_4032_, 0);
                v_bvExpr_4040_ = leanh::lean_ctor_get(v_val_4032_, 1);
                v_expr_4041_ = leanh::lean_ctor_get(v_val_4032_, 4);
                leanh::lean_inc_ref(v_bvExpr_4040_);
                leanh::lean_inc_ref(v_bvExpr_4037_);
                leanh::lean_inc_n(v_width_4039_, 2);
                v___x_4042_ = leanh::lean_apply_4(
                    v_shiftOp_4010_,
                    v_width_4036_,
                    v_width_4039_,
                    v_bvExpr_4037_,
                    v_bvExpr_4040_,
                );
                v___x_4043_ = leanh::lean_box(0);
                v___x_4044_ = l_Lean_mkConst(v_shiftOpName_4011_, v___x_4043_);
                v___x_4045_ = l_Lean_mkNatLit(v_width_4036_);
                v___x_4046_ = l_Lean_mkNatLit(v_width_4039_);
                leanh::lean_inc_ref(v_expr_4041_);
                leanh::lean_inc_ref(v_expr_4038_);
                leanh::lean_inc_ref(v___x_4046_);
                leanh::lean_inc_ref(v___x_4045_);
                v___x_4047_ = l_Lean_mkApp4(
                    v___x_4044_,
                    v___x_4045_,
                    v___x_4046_,
                    v_expr_4038_,
                    v_expr_4041_,
                );
                v___x_4048_ = l_Lean_mkConst(v_congrThm_4012_, v___x_4043_);
                v___x_4049_ = l_Lean_mkAppB(v___x_4048_, v___x_4045_, v___x_4046_);
                v___x_4050_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed as *mut core::ffi::c_void, 11, 5);
                leanh::lean_closure_set(v___x_4050_, 0, v_val_4026_);
                leanh::lean_closure_set(v___x_4050_, 1, v_val_4032_);
                leanh::lean_closure_set(v___x_4050_, 2, v_innerExpr_4009_);
                leanh::lean_closure_set(v___x_4050_, 3, v_distanceExpr_4008_);
                leanh::lean_closure_set(v___x_4050_, 4, v___x_4049_);
                v___x_4051_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4051_, 0, v_width_4036_);
                leanh::lean_ctor_set(v___x_4051_, 1, v___x_4042_);
                leanh::lean_ctor_set(v___x_4051_, 2, v_origExpr_4013_);
                leanh::lean_ctor_set(v___x_4051_, 3, v___x_4050_);
                leanh::lean_ctor_set(v___x_4051_, 4, v___x_4047_);
                if v_isShared_4035_ == 0 {
                    leanh::lean_ctor_set(v___x_4034_, 0, v___x_4051_);
                    v___x_4053_ = v___x_4034_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4051_);
                    v___x_4053_ = v_reuseFailAlloc_4057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4031_ == 0 {
                    leanh::lean_ctor_set(v___x_4030_, 0, v___x_4053_);
                    v___x_4055_ = v___x_4030_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
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
-> *mut leanh::LeanObject {
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4070_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62;
    v___x_4071_ = l_Lean_stringToMessageData(v___x_4070_);
    return v___x_4071_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71()
-> *mut leanh::LeanObject {
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4095_ = leanh::lean_box(0);
    v___x_4096_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70;
    v___x_4097_ = l_Lean_mkConst(v___x_4096_, v___x_4095_);
    return v___x_4097_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79()
-> *mut leanh::LeanObject {
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4121_ = leanh::lean_box(0);
    v___x_4122_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78;
    v___x_4123_ = l_Lean_mkConst(v___x_4122_, v___x_4121_);
    return v___x_4123_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(
    mut v_lhsExpr_4146_: *mut leanh::LeanObject,
    mut v_rhsExpr_4147_: *mut leanh::LeanObject,
    mut v_pred_4148_: u8,
    mut v_origExpr_4149_: *mut leanh::LeanObject,
    mut v_a_4150_: *mut leanh::LeanObject,
    mut v_a_4151_: *mut leanh::LeanObject,
    mut v_a_4152_: *mut leanh::LeanObject,
    mut v_a_4153_: *mut leanh::LeanObject,
    mut v_a_4154_: *mut leanh::LeanObject,
    mut v_a_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4161_: u8 = 0;
    let mut v_val_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4167_: u8 = 0;
    let mut v_val_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4174_: u8 = 0;
    let mut v_a_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4182_: u8 = 0;
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4187_: u8 = 0;
    let mut v_a_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4191_: u8 = 0;
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_lhsExpr_4146_);
                v___x_4157_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
                    v_lhsExpr_4146_,
                    v_a_4150_,
                    v_a_4151_,
                    v_a_4152_,
                    v_a_4153_,
                    v_a_4154_,
                    v_a_4155_,
                );
                if leanh::lean_obj_tag(v___x_4157_) == 0 {
                    v_a_4158_ = leanh::lean_ctor_get(v___x_4157_, 0);
                    v_isSharedCheck_4187_ = (!leanh::lean_is_exclusive(v___x_4157_)) as u8;
                    if v_isSharedCheck_4187_ == 0 {
                        v___x_4160_ = v___x_4157_;
                        v_isShared_4161_ = v_isSharedCheck_4187_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4158_);
                        leanh::lean_dec(v___x_4157_);
                        v___x_4160_ = leanh::lean_box(0);
                        v_isShared_4161_ = v_isSharedCheck_4187_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4149_);
                    leanh::lean_dec_ref(v_rhsExpr_4147_);
                    leanh::lean_dec_ref(v_lhsExpr_4146_);
                    v_a_4188_ = leanh::lean_ctor_get(v___x_4157_, 0);
                    v_isSharedCheck_4195_ = (!leanh::lean_is_exclusive(v___x_4157_)) as u8;
                    if v_isSharedCheck_4195_ == 0 {
                        v___x_4190_ = v___x_4157_;
                        v_isShared_4191_ = v_isSharedCheck_4195_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4188_);
                        leanh::lean_dec(v___x_4157_);
                        v___x_4190_ = leanh::lean_box(0);
                        v_isShared_4191_ = v_isSharedCheck_4195_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4158_) == 1 {
                    leanh::lean_del_object(v___x_4160_);
                    v_val_4162_ = leanh::lean_ctor_get(v_a_4158_, 0);
                    leanh::lean_inc(v_val_4162_);
                    leanh::lean_dec_ref_known(v_a_4158_, 1);
                    leanh::lean_inc_ref(v_rhsExpr_4147_);
                    v___x_4163_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
                        v_rhsExpr_4147_,
                        v_a_4150_,
                        v_a_4151_,
                        v_a_4152_,
                        v_a_4153_,
                        v_a_4154_,
                        v_a_4155_,
                    );
                    if leanh::lean_obj_tag(v___x_4163_) == 0 {
                        v_a_4164_ = leanh::lean_ctor_get(v___x_4163_, 0);
                        v_isSharedCheck_4174_ =
                            (!leanh::lean_is_exclusive(v___x_4163_)) as u8;
                        if v_isSharedCheck_4174_ == 0 {
                            v___x_4166_ = v___x_4163_;
                            v_isShared_4167_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4164_);
                            leanh::lean_dec(v___x_4163_);
                            v___x_4166_ = leanh::lean_box(0);
                            v_isShared_4167_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4162_);
                        leanh::lean_dec_ref(v_origExpr_4149_);
                        leanh::lean_dec_ref(v_rhsExpr_4147_);
                        leanh::lean_dec_ref(v_lhsExpr_4146_);
                        v_a_4175_ = leanh::lean_ctor_get(v___x_4163_, 0);
                        v_isSharedCheck_4182_ =
                            (!leanh::lean_is_exclusive(v___x_4163_)) as u8;
                        if v_isSharedCheck_4182_ == 0 {
                            v___x_4177_ = v___x_4163_;
                            v_isShared_4178_ = v_isSharedCheck_4182_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4175_);
                            leanh::lean_dec(v___x_4163_);
                            v___x_4177_ = leanh::lean_box(0);
                            v_isShared_4178_ = v_isSharedCheck_4182_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4158_);
                    leanh::lean_dec_ref(v_origExpr_4149_);
                    leanh::lean_dec_ref(v_rhsExpr_4147_);
                    leanh::lean_dec_ref(v_lhsExpr_4146_);
                    v___x_4183_ = leanh::lean_box(0);
                    if v_isShared_4161_ == 0 {
                        leanh::lean_ctor_set(v___x_4160_, 0, v___x_4183_);
                        v___x_4185_ = v___x_4160_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
                        v___x_4185_ = v_reuseFailAlloc_4186_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4164_) == 1 {
                    leanh::lean_del_object(v___x_4166_);
                    v_val_4168_ = leanh::lean_ctor_get(v_a_4164_, 0);
                    leanh::lean_inc(v_val_4168_);
                    leanh::lean_dec_ref_known(v_a_4164_, 1);
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
                    leanh::lean_dec(v_a_4164_);
                    leanh::lean_dec(v_val_4162_);
                    leanh::lean_dec_ref(v_origExpr_4149_);
                    leanh::lean_dec_ref(v_rhsExpr_4147_);
                    leanh::lean_dec_ref(v_lhsExpr_4146_);
                    v___x_4170_ = leanh::lean_box(0);
                    if v_isShared_4167_ == 0 {
                        leanh::lean_ctor_set(v___x_4166_, 0, v___x_4170_);
                        v___x_4172_ = v___x_4166_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
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
                    v_reuseFailAlloc_4181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
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
                    v_reuseFailAlloc_4194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
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
    mut v_origExpr_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_a_4198_: *mut leanh::LeanObject,
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
    mut v_a_4201_: *mut leanh::LeanObject,
    mut v_a_4202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: u8 = 0;
    let mut v_arg_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: u8 = 0;
    let mut v_arg_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: u8 = 0;
    let mut v___x_4230_: u8 = 0;
    let mut v_arg_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: u8 = 0;
    let mut v___x_4240_: u8 = 0;
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: u8 = 0;
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v_val_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v_val_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4258_: u8 = 0;
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4263_: u8 = 0;
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v_a_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut v_isSharedCheck_4279_: u8 = 0;
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4284_: u8 = 0;
    let mut v_a_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4288_: u8 = 0;
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut v_a_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4301_: u8 = 0;
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut v_isSharedCheck_4306_: u8 = 0;
    let mut v_a_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4310_: u8 = 0;
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_origExpr_4196_);
                v___x_4207_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_4196_, v_a_4200_);
                if leanh::lean_obj_tag(v___x_4207_) == 0 {
                    v_a_4208_ = leanh::lean_ctor_get(v___x_4207_, 0);
                    v_isSharedCheck_4306_ = (!leanh::lean_is_exclusive(v___x_4207_)) as u8;
                    if v_isSharedCheck_4306_ == 0 {
                        v___x_4210_ = v___x_4207_;
                        v_isShared_4211_ = v_isSharedCheck_4306_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4208_);
                        leanh::lean_dec(v___x_4207_);
                        v___x_4210_ = leanh::lean_box(0);
                        v_isShared_4211_ = v_isSharedCheck_4306_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4196_);
                    v_a_4307_ = leanh::lean_ctor_get(v___x_4207_, 0);
                    v_isSharedCheck_4314_ = (!leanh::lean_is_exclusive(v___x_4207_)) as u8;
                    if v_isSharedCheck_4314_ == 0 {
                        v___x_4309_ = v___x_4207_;
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4307_);
                        leanh::lean_dec(v___x_4207_);
                        v___x_4309_ = leanh::lean_box(0);
                        v_isShared_4310_ = v_isSharedCheck_4314_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4205_ = leanh::lean_box(0);
                v___x_4206_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4206_, 0, v___x_4205_);
                return v___x_4206_;
            }
            2 => {
                v___x_4217_ = l_Lean_Expr_cleanupAnnotations(v_a_4208_);
                v___x_4218_ = l_Lean_Expr_isApp(v___x_4217_);
                if v___x_4218_ == 0 {
                    leanh::lean_dec_ref(v___x_4217_);
                    leanh::lean_dec_ref(v_origExpr_4196_);
                    state = 3;
                    continue;
                } else {
                    v_arg_4219_ = leanh::lean_ctor_get(v___x_4217_, 1);
                    leanh::lean_inc_ref(v_arg_4219_);
                    v___x_4220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4217_);
                    v___x_4221_ = l_Lean_Expr_isApp(v___x_4220_);
                    if v___x_4221_ == 0 {
                        leanh::lean_dec_ref(v___x_4220_);
                        leanh::lean_dec_ref(v_arg_4219_);
                        leanh::lean_dec_ref(v_origExpr_4196_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_4222_ = leanh::lean_ctor_get(v___x_4220_, 1);
                        leanh::lean_inc_ref(v_arg_4222_);
                        v___x_4223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4220_);
                        v___x_4224_ = l_Lean_Expr_isApp(v___x_4223_);
                        if v___x_4224_ == 0 {
                            leanh::lean_dec_ref(v___x_4223_);
                            leanh::lean_dec_ref(v_arg_4222_);
                            leanh::lean_dec_ref(v_arg_4219_);
                            leanh::lean_dec_ref(v_origExpr_4196_);
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
                                        leanh::lean_dec_ref(v___x_4225_);
                                        leanh::lean_dec_ref(v_arg_4222_);
                                        leanh::lean_dec_ref(v_arg_4219_);
                                        leanh::lean_dec_ref(v_origExpr_4196_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v_arg_4231_ = leanh::lean_ctor_get(v___x_4225_, 1);
                                        leanh::lean_inc_ref(v_arg_4231_);
                                        v___x_4232_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4225_);
                                        v___x_4233_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7;
                                        v___x_4234_ =
                                            l_Lean_Expr_isConstOf(v___x_4232_, v___x_4233_);
                                        leanh::lean_dec_ref(v___x_4232_);
                                        if v___x_4234_ == 0 {
                                            leanh::lean_dec_ref(v_arg_4231_);
                                            leanh::lean_dec_ref(v_arg_4222_);
                                            leanh::lean_dec_ref(v_arg_4219_);
                                            leanh::lean_dec_ref(v_origExpr_4196_);
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_del_object(v___x_4210_);
                                            v___x_4235_ =
                                                l_Lean_Expr_cleanupAnnotations(v_arg_4231_);
                                            v___x_4236_ = l_Lean_Expr_isApp(v___x_4235_);
                                            if v___x_4236_ == 0 {
                                                leanh::lean_dec_ref(v___x_4235_);
                                                leanh::lean_dec_ref(v_arg_4222_);
                                                leanh::lean_dec_ref(v_arg_4219_);
                                                leanh::lean_dec_ref(v_origExpr_4196_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_4237_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_4235_);
                                                v___x_4238_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                                                v___x_4239_ =
                                                    l_Lean_Expr_isConstOf(v___x_4237_, v___x_4238_);
                                                leanh::lean_dec_ref(v___x_4237_);
                                                if v___x_4239_ == 0 {
                                                    leanh::lean_dec_ref(v_arg_4222_);
                                                    leanh::lean_dec_ref(v_arg_4219_);
                                                    leanh::lean_dec_ref(v_origExpr_4196_);
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
                                    leanh::lean_dec_ref(v___x_4225_);
                                    leanh::lean_del_object(v___x_4210_);
                                    v___x_4242_ = 1;
                                    v___x_4243_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_arg_4222_, v_arg_4219_, v___x_4242_, v_origExpr_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
                                    return v___x_4243_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4225_);
                                leanh::lean_del_object(v___x_4210_);
                                leanh::lean_inc_ref(v_arg_4222_);
                                v___x_4244_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
                                    v_arg_4222_,
                                    v_a_4197_,
                                    v_a_4198_,
                                    v_a_4199_,
                                    v_a_4200_,
                                    v_a_4201_,
                                    v_a_4202_,
                                );
                                if leanh::lean_obj_tag(v___x_4244_) == 0 {
                                    v_a_4245_ = leanh::lean_ctor_get(v___x_4244_, 0);
                                    v_isSharedCheck_4297_ =
                                        (!leanh::lean_is_exclusive(v___x_4244_)) as u8;
                                    if v_isSharedCheck_4297_ == 0 {
                                        v___x_4247_ = v___x_4244_;
                                        v_isShared_4248_ = v_isSharedCheck_4297_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4245_);
                                        leanh::lean_dec(v___x_4244_);
                                        v___x_4247_ = leanh::lean_box(0);
                                        v_isShared_4248_ = v_isSharedCheck_4297_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_4222_);
                                    leanh::lean_dec_ref(v_arg_4219_);
                                    leanh::lean_dec_ref(v_origExpr_4196_);
                                    v_a_4298_ = leanh::lean_ctor_get(v___x_4244_, 0);
                                    v_isSharedCheck_4305_ =
                                        (!leanh::lean_is_exclusive(v___x_4244_)) as u8;
                                    if v_isSharedCheck_4305_ == 0 {
                                        v___x_4300_ = v___x_4244_;
                                        v_isShared_4301_ = v_isSharedCheck_4305_;
                                        state = 17;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4298_);
                                        leanh::lean_dec(v___x_4244_);
                                        v___x_4300_ = leanh::lean_box(0);
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
                v___x_4213_ = leanh::lean_box(0);
                if v_isShared_4211_ == 0 {
                    leanh::lean_ctor_set(v___x_4210_, 0, v___x_4213_);
                    v___x_4215_ = v___x_4210_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
                    v___x_4215_ = v_reuseFailAlloc_4216_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4215_;
            }
            5 => {
                if leanh::lean_obj_tag(v_a_4245_) == 1 {
                    leanh::lean_del_object(v___x_4247_);
                    v_val_4249_ = leanh::lean_ctor_get(v_a_4245_, 0);
                    leanh::lean_inc(v_val_4249_);
                    leanh::lean_dec_ref_known(v_a_4245_, 1);
                    v___x_4250_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_4219_,
                        v_a_4199_,
                        v_a_4200_,
                        v_a_4201_,
                        v_a_4202_,
                    );
                    leanh::lean_dec_ref(v_arg_4219_);
                    if leanh::lean_obj_tag(v___x_4250_) == 0 {
                        v_a_4251_ = leanh::lean_ctor_get(v___x_4250_, 0);
                        v_isSharedCheck_4284_ =
                            (!leanh::lean_is_exclusive(v___x_4250_)) as u8;
                        if v_isSharedCheck_4284_ == 0 {
                            v___x_4253_ = v___x_4250_;
                            v_isShared_4254_ = v_isSharedCheck_4284_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4251_);
                            leanh::lean_dec(v___x_4250_);
                            v___x_4253_ = leanh::lean_box(0);
                            v_isShared_4254_ = v_isSharedCheck_4284_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4249_);
                        leanh::lean_dec_ref(v_arg_4222_);
                        leanh::lean_dec_ref(v_origExpr_4196_);
                        v_a_4285_ = leanh::lean_ctor_get(v___x_4250_, 0);
                        v_isSharedCheck_4292_ =
                            (!leanh::lean_is_exclusive(v___x_4250_)) as u8;
                        if v_isSharedCheck_4292_ == 0 {
                            v___x_4287_ = v___x_4250_;
                            v_isShared_4288_ = v_isSharedCheck_4292_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4285_);
                            leanh::lean_dec(v___x_4250_);
                            v___x_4287_ = leanh::lean_box(0);
                            v_isShared_4288_ = v_isSharedCheck_4292_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4245_);
                    leanh::lean_dec_ref(v_arg_4222_);
                    leanh::lean_dec_ref(v_arg_4219_);
                    leanh::lean_dec_ref(v_origExpr_4196_);
                    v___x_4293_ = leanh::lean_box(0);
                    if v_isShared_4248_ == 0 {
                        leanh::lean_ctor_set(v___x_4247_, 0, v___x_4293_);
                        v___x_4295_ = v___x_4247_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
                        v___x_4295_ = v_reuseFailAlloc_4296_;
                        state = 16;
                        continue;
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_a_4251_) == 1 {
                    leanh::lean_del_object(v___x_4253_);
                    v_val_4255_ = leanh::lean_ctor_get(v_a_4251_, 0);
                    v_isSharedCheck_4279_ = (!leanh::lean_is_exclusive(v_a_4251_)) as u8;
                    if v_isSharedCheck_4279_ == 0 {
                        v___x_4257_ = v_a_4251_;
                        v_isShared_4258_ = v_isSharedCheck_4279_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4255_);
                        leanh::lean_dec(v_a_4251_);
                        v___x_4257_ = leanh::lean_box(0);
                        v_isShared_4258_ = v_isSharedCheck_4279_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4251_);
                    leanh::lean_dec(v_val_4249_);
                    leanh::lean_dec_ref(v_arg_4222_);
                    leanh::lean_dec_ref(v_origExpr_4196_);
                    v___x_4280_ = leanh::lean_box(0);
                    if v_isShared_4254_ == 0 {
                        leanh::lean_ctor_set(v___x_4253_, 0, v___x_4280_);
                        v___x_4282_ = v___x_4253_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
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
                if leanh::lean_obj_tag(v___x_4259_) == 0 {
                    v_a_4260_ = leanh::lean_ctor_get(v___x_4259_, 0);
                    v_isSharedCheck_4270_ = (!leanh::lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4270_ == 0 {
                        v___x_4262_ = v___x_4259_;
                        v_isShared_4263_ = v_isSharedCheck_4270_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4260_);
                        leanh::lean_dec(v___x_4259_);
                        v___x_4262_ = leanh::lean_box(0);
                        v_isShared_4263_ = v_isSharedCheck_4270_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4257_);
                    v_a_4271_ = leanh::lean_ctor_get(v___x_4259_, 0);
                    v_isSharedCheck_4278_ = (!leanh::lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4278_ == 0 {
                        v___x_4273_ = v___x_4259_;
                        v_isShared_4274_ = v_isSharedCheck_4278_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4271_);
                        leanh::lean_dec(v___x_4259_);
                        v___x_4273_ = leanh::lean_box(0);
                        v_isShared_4274_ = v_isSharedCheck_4278_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4258_ == 0 {
                    leanh::lean_ctor_set(v___x_4257_, 0, v_a_4260_);
                    v___x_4265_ = v___x_4257_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4260_);
                    v___x_4265_ = v_reuseFailAlloc_4269_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4263_ == 0 {
                    leanh::lean_ctor_set(v___x_4262_, 0, v___x_4265_);
                    v___x_4267_ = v___x_4262_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
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
                    v_reuseFailAlloc_4277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
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
                    v_reuseFailAlloc_4291_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
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
                    v_reuseFailAlloc_4304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
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
                    v_reuseFailAlloc_4313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
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
    mut v_e_4315_: *mut leanh::LeanObject,
    mut v_a_4316_: *mut leanh::LeanObject,
    mut v_a_4317_: *mut leanh::LeanObject,
    mut v_a_4318_: *mut leanh::LeanObject,
    mut v_a_4319_: *mut leanh::LeanObject,
    mut v_a_4320_: *mut leanh::LeanObject,
    mut v_a_4321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4328_: u8 = 0;
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4356_: u8 = 0;
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4360_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4347_ = lean_st_ref_get(v_a_4316_);
                v_bvPredCache_4348_ = leanh::lean_ctor_get(v___x_4347_, 2);
                leanh::lean_inc_ref(v_bvPredCache_4348_);
                leanh::lean_dec(v___x_4347_);
                v___x_4349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvPredCache_4348_, v_e_4315_);
                leanh::lean_dec_ref(v_bvPredCache_4348_);
                if leanh::lean_obj_tag(v___x_4349_) == 0 {
                    leanh::lean_inc_ref(v_e_4315_);
                    v___x_4350_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_e_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_);
                    if leanh::lean_obj_tag(v___x_4350_) == 0 {
                        v_a_4351_ = leanh::lean_ctor_get(v___x_4350_, 0);
                        leanh::lean_inc(v_a_4351_);
                        if leanh::lean_obj_tag(v_a_4351_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4350_, 1);
                            leanh::lean_inc_ref(v_e_4315_);
                            v___x_4352_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(
                                v_e_4315_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_,
                            );
                            v___y_4324_ = v___x_4352_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_a_4351_, 1);
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
                    leanh::lean_dec_ref(v_e_4315_);
                    v_val_4353_ = leanh::lean_ctor_get(v___x_4349_, 0);
                    v_isSharedCheck_4360_ = (!leanh::lean_is_exclusive(v___x_4349_)) as u8;
                    if v_isSharedCheck_4360_ == 0 {
                        v___x_4355_ = v___x_4349_;
                        v_isShared_4356_ = v_isSharedCheck_4360_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4353_);
                        leanh::lean_dec(v___x_4349_);
                        v___x_4355_ = leanh::lean_box(0);
                        v_isShared_4356_ = v_isSharedCheck_4360_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4324_) == 0 {
                    v_a_4325_ = leanh::lean_ctor_get(v___y_4324_, 0);
                    v_isSharedCheck_4346_ = (!leanh::lean_is_exclusive(v___y_4324_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v___x_4327_ = v___y_4324_;
                        v_isShared_4328_ = v_isSharedCheck_4346_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4325_);
                        leanh::lean_dec(v___y_4324_);
                        v___x_4327_ = leanh::lean_box(0);
                        v_isShared_4328_ = v_isSharedCheck_4346_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4315_);
                    return v___y_4324_;
                }
            }
            2 => {
                v___x_4329_ = lean_st_ref_take(v_a_4316_);
                v_lemmas_4330_ = leanh::lean_ctor_get(v___x_4329_, 0);
                v_bvExprCache_4331_ = leanh::lean_ctor_get(v___x_4329_, 1);
                v_bvPredCache_4332_ = leanh::lean_ctor_get(v___x_4329_, 2);
                v_bvLogicalCache_4333_ = leanh::lean_ctor_get(v___x_4329_, 3);
                v_isSharedCheck_4345_ = (!leanh::lean_is_exclusive(v___x_4329_)) as u8;
                if v_isSharedCheck_4345_ == 0 {
                    v___x_4335_ = v___x_4329_;
                    v_isShared_4336_ = v_isSharedCheck_4345_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_bvLogicalCache_4333_);
                    leanh::lean_inc(v_bvPredCache_4332_);
                    leanh::lean_inc(v_bvExprCache_4331_);
                    leanh::lean_inc(v_lemmas_4330_);
                    leanh::lean_dec(v___x_4329_);
                    v___x_4335_ = leanh::lean_box(0);
                    v_isShared_4336_ = v_isSharedCheck_4345_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_4325_);
                v___x_4337_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvPredCache_4332_, v_e_4315_, v_a_4325_);
                if v_isShared_4336_ == 0 {
                    leanh::lean_ctor_set(v___x_4335_, 2, v___x_4337_);
                    v___x_4339_ = v___x_4335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4344_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_lemmas_4330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 1, v_bvExprCache_4331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 2, v___x_4337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 3, v_bvLogicalCache_4333_);
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
                    v_reuseFailAlloc_4343_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4325_);
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
                    leanh::lean_ctor_set_tag(v___x_4355_, 0);
                    v___x_4358_ = v___x_4355_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4359_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_val_4353_);
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
    mut v_origExpr_4361_: *mut leanh::LeanObject,
    mut v_a_4362_: *mut leanh::LeanObject,
    mut v_a_4363_: *mut leanh::LeanObject,
    mut v_a_4364_: *mut leanh::LeanObject,
    mut v_a_4365_: *mut leanh::LeanObject,
    mut v_a_4366_: *mut leanh::LeanObject,
    mut v_a_4367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4369_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(v_origExpr_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
    return v___x_4369_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(
    mut v_origExpr_4370_: *mut leanh::LeanObject,
    mut v_a_4371_: *mut leanh::LeanObject,
    mut v_a_4372_: *mut leanh::LeanObject,
    mut v_a_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
    mut v_a_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4382_: u8 = 0;
    let mut v_val_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4386_: u8 = 0;
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4391_: u8 = 0;
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_a_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_a_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_4378_) == 0 {
                    v_a_4379_ = leanh::lean_ctor_get(v___x_4378_, 0);
                    v_isSharedCheck_4412_ = (!leanh::lean_is_exclusive(v___x_4378_)) as u8;
                    if v_isSharedCheck_4412_ == 0 {
                        v___x_4381_ = v___x_4378_;
                        v_isShared_4382_ = v_isSharedCheck_4412_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4379_);
                        leanh::lean_dec(v___x_4378_);
                        v___x_4381_ = leanh::lean_box(0);
                        v_isShared_4382_ = v_isSharedCheck_4412_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4413_ = leanh::lean_ctor_get(v___x_4378_, 0);
                    v_isSharedCheck_4420_ = (!leanh::lean_is_exclusive(v___x_4378_)) as u8;
                    if v_isSharedCheck_4420_ == 0 {
                        v___x_4415_ = v___x_4378_;
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4413_);
                        leanh::lean_dec(v___x_4378_);
                        v___x_4415_ = leanh::lean_box(0);
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4379_) == 1 {
                    leanh::lean_del_object(v___x_4381_);
                    v_val_4383_ = leanh::lean_ctor_get(v_a_4379_, 0);
                    v_isSharedCheck_4407_ = (!leanh::lean_is_exclusive(v_a_4379_)) as u8;
                    if v_isSharedCheck_4407_ == 0 {
                        v___x_4385_ = v_a_4379_;
                        v_isShared_4386_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4383_);
                        leanh::lean_dec(v_a_4379_);
                        v___x_4385_ = leanh::lean_box(0);
                        v_isShared_4386_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4379_);
                    v___x_4408_ = leanh::lean_box(0);
                    if v_isShared_4382_ == 0 {
                        leanh::lean_ctor_set(v___x_4381_, 0, v___x_4408_);
                        v___x_4410_ = v___x_4381_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4408_);
                        v___x_4410_ = v_reuseFailAlloc_4411_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4387_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_4383_);
                if leanh::lean_obj_tag(v___x_4387_) == 0 {
                    v_a_4388_ = leanh::lean_ctor_get(v___x_4387_, 0);
                    v_isSharedCheck_4398_ = (!leanh::lean_is_exclusive(v___x_4387_)) as u8;
                    if v_isSharedCheck_4398_ == 0 {
                        v___x_4390_ = v___x_4387_;
                        v_isShared_4391_ = v_isSharedCheck_4398_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4388_);
                        leanh::lean_dec(v___x_4387_);
                        v___x_4390_ = leanh::lean_box(0);
                        v_isShared_4391_ = v_isSharedCheck_4398_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4385_);
                    v_a_4399_ = leanh::lean_ctor_get(v___x_4387_, 0);
                    v_isSharedCheck_4406_ = (!leanh::lean_is_exclusive(v___x_4387_)) as u8;
                    if v_isSharedCheck_4406_ == 0 {
                        v___x_4401_ = v___x_4387_;
                        v_isShared_4402_ = v_isSharedCheck_4406_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4399_);
                        leanh::lean_dec(v___x_4387_);
                        v___x_4401_ = leanh::lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4406_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4386_ == 0 {
                    leanh::lean_ctor_set(v___x_4385_, 0, v_a_4388_);
                    v___x_4393_ = v___x_4385_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4388_);
                    v___x_4393_ = v_reuseFailAlloc_4397_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4391_ == 0 {
                    leanh::lean_ctor_set(v___x_4390_, 0, v___x_4393_);
                    v___x_4395_ = v___x_4390_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4393_);
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
                    v_reuseFailAlloc_4405_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
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
                    v_reuseFailAlloc_4419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
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
    mut v_lhsExpr_4433_: *mut leanh::LeanObject,
    mut v_rhsExpr_4434_: *mut leanh::LeanObject,
    mut v_gate_4435_: u8,
    mut v_origExpr_4436_: *mut leanh::LeanObject,
    mut v_a_4437_: *mut leanh::LeanObject,
    mut v_a_4438_: *mut leanh::LeanObject,
    mut v_a_4439_: *mut leanh::LeanObject,
    mut v_a_4440_: *mut leanh::LeanObject,
    mut v_a_4441_: *mut leanh::LeanObject,
    mut v_a_4442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4448_: u8 = 0;
    let mut v_val_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v_val_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_a_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_lhsExpr_4433_);
                v___x_4444_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_lhsExpr_4433_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
                if leanh::lean_obj_tag(v___x_4444_) == 0 {
                    v_a_4445_ = leanh::lean_ctor_get(v___x_4444_, 0);
                    v_isSharedCheck_4489_ = (!leanh::lean_is_exclusive(v___x_4444_)) as u8;
                    if v_isSharedCheck_4489_ == 0 {
                        v___x_4447_ = v___x_4444_;
                        v_isShared_4448_ = v_isSharedCheck_4489_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4445_);
                        leanh::lean_dec(v___x_4444_);
                        v___x_4447_ = leanh::lean_box(0);
                        v_isShared_4448_ = v_isSharedCheck_4489_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4436_);
                    leanh::lean_dec_ref(v_rhsExpr_4434_);
                    leanh::lean_dec_ref(v_lhsExpr_4433_);
                    return v___x_4444_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4445_) == 1 {
                    leanh::lean_del_object(v___x_4447_);
                    v_val_4449_ = leanh::lean_ctor_get(v_a_4445_, 0);
                    leanh::lean_inc(v_val_4449_);
                    leanh::lean_dec_ref_known(v_a_4445_, 1);
                    leanh::lean_inc_ref(v_rhsExpr_4434_);
                    v___x_4450_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_rhsExpr_4434_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_);
                    if leanh::lean_obj_tag(v___x_4450_) == 0 {
                        v_a_4451_ = leanh::lean_ctor_get(v___x_4450_, 0);
                        v_isSharedCheck_4484_ =
                            (!leanh::lean_is_exclusive(v___x_4450_)) as u8;
                        if v_isSharedCheck_4484_ == 0 {
                            v___x_4453_ = v___x_4450_;
                            v_isShared_4454_ = v_isSharedCheck_4484_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4451_);
                            leanh::lean_dec(v___x_4450_);
                            v___x_4453_ = leanh::lean_box(0);
                            v_isShared_4454_ = v_isSharedCheck_4484_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4449_);
                        leanh::lean_dec_ref(v_origExpr_4436_);
                        leanh::lean_dec_ref(v_rhsExpr_4434_);
                        leanh::lean_dec_ref(v_lhsExpr_4433_);
                        return v___x_4450_;
                    }
                } else {
                    leanh::lean_dec(v_a_4445_);
                    leanh::lean_dec_ref(v_origExpr_4436_);
                    leanh::lean_dec_ref(v_rhsExpr_4434_);
                    leanh::lean_dec_ref(v_lhsExpr_4433_);
                    v___x_4485_ = leanh::lean_box(0);
                    if v_isShared_4448_ == 0 {
                        leanh::lean_ctor_set(v___x_4447_, 0, v___x_4485_);
                        v___x_4487_ = v___x_4447_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4488_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
                        v___x_4487_ = v_reuseFailAlloc_4488_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4451_) == 1 {
                    leanh::lean_del_object(v___x_4453_);
                    v_val_4455_ = leanh::lean_ctor_get(v_a_4451_, 0);
                    v_isSharedCheck_4479_ = (!leanh::lean_is_exclusive(v_a_4451_)) as u8;
                    if v_isSharedCheck_4479_ == 0 {
                        v___x_4457_ = v_a_4451_;
                        v_isShared_4458_ = v_isSharedCheck_4479_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4455_);
                        leanh::lean_dec(v_a_4451_);
                        v___x_4457_ = leanh::lean_box(0);
                        v_isShared_4458_ = v_isSharedCheck_4479_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4451_);
                    leanh::lean_dec(v_val_4449_);
                    leanh::lean_dec_ref(v_origExpr_4436_);
                    leanh::lean_dec_ref(v_rhsExpr_4434_);
                    leanh::lean_dec_ref(v_lhsExpr_4433_);
                    v___x_4480_ = leanh::lean_box(0);
                    if v_isShared_4454_ == 0 {
                        leanh::lean_ctor_set(v___x_4453_, 0, v___x_4480_);
                        v___x_4482_ = v___x_4453_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
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
                if leanh::lean_obj_tag(v___x_4459_) == 0 {
                    v_a_4460_ = leanh::lean_ctor_get(v___x_4459_, 0);
                    v_isSharedCheck_4470_ = (!leanh::lean_is_exclusive(v___x_4459_)) as u8;
                    if v_isSharedCheck_4470_ == 0 {
                        v___x_4462_ = v___x_4459_;
                        v_isShared_4463_ = v_isSharedCheck_4470_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4460_);
                        leanh::lean_dec(v___x_4459_);
                        v___x_4462_ = leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4470_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4457_);
                    v_a_4471_ = leanh::lean_ctor_get(v___x_4459_, 0);
                    v_isSharedCheck_4478_ = (!leanh::lean_is_exclusive(v___x_4459_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4473_ = v___x_4459_;
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4471_);
                        leanh::lean_dec(v___x_4459_);
                        v___x_4473_ = leanh::lean_box(0);
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4458_ == 0 {
                    leanh::lean_ctor_set(v___x_4457_, 0, v_a_4460_);
                    v___x_4465_ = v___x_4457_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4460_);
                    v___x_4465_ = v_reuseFailAlloc_4469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4463_ == 0 {
                    leanh::lean_ctor_set(v___x_4462_, 0, v___x_4465_);
                    v___x_4467_ = v___x_4462_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4468_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 0, v___x_4465_);
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
                    v_reuseFailAlloc_4477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
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
    mut v_origExpr_4490_: *mut leanh::LeanObject,
    mut v_a_4491_: *mut leanh::LeanObject,
    mut v_a_4492_: *mut leanh::LeanObject,
    mut v_a_4493_: *mut leanh::LeanObject,
    mut v_a_4494_: *mut leanh::LeanObject,
    mut v_a_4495_: *mut leanh::LeanObject,
    mut v_a_4496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: u8 = 0;
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: u8 = 0;
    let mut v___x_4510_: u8 = 0;
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: u8 = 0;
    let mut v___x_4516_: u8 = 0;
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: u8 = 0;
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: u8 = 0;
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: u8 = 0;
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4542_: u8 = 0;
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u8 = 0;
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v___x_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4552_: u8 = 0;
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4556_: u8 = 0;
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4561_: u8 = 0;
    let mut v_val_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4567_: u8 = 0;
    let mut v_val_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4573_: u8 = 0;
    let mut v_val_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4589_: u8 = 0;
    let mut v_a_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4593_: u8 = 0;
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4597_: u8 = 0;
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4608_: u8 = 0;
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4613_: u8 = 0;
    let mut v___x_4614_: u8 = 0;
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: u8 = 0;
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v_val_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4638_: u8 = 0;
    let mut v_a_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut v_isSharedCheck_4647_: u8 = 0;
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4657_: u8 = 0;
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_a_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4676_: u8 = 0;
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut v_a_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_a_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4693_: u8 = 0;
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4697_: u8 = 0;
    let mut v_a_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4701_: u8 = 0;
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4501_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0;
                v___x_4502_ = l_Lean_Core_checkSystem(v___x_4501_, v_a_4495_, v_a_4496_);
                if leanh::lean_obj_tag(v___x_4502_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4502_, 1);
                    leanh::lean_inc_ref(v_origExpr_4490_);
                    v___x_4503_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_4490_, v_a_4494_);
                    if leanh::lean_obj_tag(v___x_4503_) == 0 {
                        v_a_4504_ = leanh::lean_ctor_get(v___x_4503_, 0);
                        leanh::lean_inc(v_a_4504_);
                        leanh::lean_dec_ref_known(v___x_4503_, 1);
                        v___x_4505_ = l_Lean_Expr_cleanupAnnotations(v_a_4504_);
                        v___x_4506_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3;
                        v___x_4507_ = l_Lean_Expr_isConstOf(v___x_4505_, v___x_4506_);
                        if v___x_4507_ == 0 {
                            v___x_4508_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5;
                            v___x_4509_ = l_Lean_Expr_isConstOf(v___x_4505_, v___x_4508_);
                            if v___x_4509_ == 0 {
                                v___x_4510_ = l_Lean_Expr_isApp(v___x_4505_);
                                if v___x_4510_ == 0 {
                                    leanh::lean_dec_ref(v___x_4505_);
                                    v___x_4511_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                    return v___x_4511_;
                                } else {
                                    v_arg_4512_ = leanh::lean_ctor_get(v___x_4505_, 1);
                                    leanh::lean_inc_ref(v_arg_4512_);
                                    v___x_4513_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4505_);
                                    v___x_4514_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6;
                                    v___x_4515_ = l_Lean_Expr_isConstOf(v___x_4513_, v___x_4514_);
                                    if v___x_4515_ == 0 {
                                        v___x_4516_ = l_Lean_Expr_isApp(v___x_4513_);
                                        if v___x_4516_ == 0 {
                                            leanh::lean_dec_ref(v___x_4513_);
                                            leanh::lean_dec_ref(v_arg_4512_);
                                            v___x_4517_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                            return v___x_4517_;
                                        } else {
                                            v_arg_4518_ =
                                                leanh::lean_ctor_get(v___x_4513_, 1);
                                            leanh::lean_inc_ref(v_arg_4518_);
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
                                                        leanh::lean_dec_ref(v___x_4519_);
                                                        leanh::lean_dec_ref(v_arg_4518_);
                                                        leanh::lean_dec_ref(v_arg_4512_);
                                                        v___x_4525_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                        return v___x_4525_;
                                                    } else {
                                                        v_arg_4526_ = leanh::lean_ctor_get(
                                                            v___x_4519_,
                                                            1,
                                                        );
                                                        leanh::lean_inc_ref(v_arg_4526_);
                                                        v___x_4527_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_4519_,
                                                            );
                                                        v___x_4528_ =
                                                            l_Lean_Expr_isApp(v___x_4527_);
                                                        if v___x_4528_ == 0 {
                                                            leanh::lean_dec_ref(v___x_4527_);
                                                            leanh::lean_dec_ref(v_arg_4526_);
                                                            leanh::lean_dec_ref(v_arg_4518_);
                                                            leanh::lean_dec_ref(v_arg_4512_);
                                                            v___x_4529_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                            return v___x_4529_;
                                                        } else {
                                                            v_arg_4530_ =
                                                                leanh::lean_ctor_get(
                                                                    v___x_4527_,
                                                                    1,
                                                                );
                                                            leanh::lean_inc_ref(v_arg_4530_);
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
                                                                leanh::lean_dec_ref(
                                                                    v_arg_4526_,
                                                                );
                                                                v___x_4534_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7;
                                                                v___x_4535_ = l_Lean_Expr_isConstOf(
                                                                    v___x_4531_,
                                                                    v___x_4534_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v___x_4531_,
                                                                );
                                                                if v___x_4535_ == 0 {
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_4530_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_4518_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_4512_,
                                                                    );
                                                                    v___x_4536_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                    return v___x_4536_;
                                                                } else {
                                                                    v___x_4537_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_4530_, v_a_4494_);
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_4537_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_4538_ = leanh::lean_ctor_get(v___x_4537_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_4538_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_4537_, 1);
                                                                        v___x_4539_ = l_Lean_Expr_cleanupAnnotations(v_a_4538_);
                                                                        v___x_4540_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11;
                                                                        v___x_4541_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_4539_,
                                                                                v___x_4540_,
                                                                            );
                                                                        if v___x_4541_ == 0 {
                                                                            leanh::lean_dec_ref(v_arg_4518_);
                                                                            leanh::lean_dec_ref(v_arg_4512_);
                                                                            v___x_4542_ =
                                                                                l_Lean_Expr_isApp(
                                                                                    v___x_4539_,
                                                                                );
                                                                            if v___x_4542_ == 0 {
                                                                                leanh::lean_dec_ref(v___x_4539_);
                                                                                leanh::lean_dec_ref(v_origExpr_4490_);
                                                                                state = 1;
                                                                                continue;
                                                                            } else {
                                                                                v___x_4543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4539_);
                                                                                v___x_4544_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                                                                                v___x_4545_ = l_Lean_Expr_isConstOf(v___x_4543_, v___x_4544_);
                                                                                leanh::lean_dec_ref(v___x_4543_);
                                                                                if v___x_4545_ == 0
                                                                                {
                                                                                    leanh::lean_dec_ref(v_origExpr_4490_);
                                                                                    state = 1;
                                                                                    continue;
                                                                                } else {
                                                                                    v___x_4546_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                                    return v___x_4546_;
                                                                                }
                                                                            }
                                                                        } else {
                                                                            leanh::lean_dec_ref(v___x_4539_);
                                                                            v___x_4547_ = 2;
                                                                            v___x_4548_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_4518_, v_arg_4512_, v___x_4547_, v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                            return v___x_4548_;
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_4518_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_4512_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_origExpr_4490_,
                                                                        );
                                                                        v_a_4549_ = leanh::lean_ctor_get(v___x_4537_, 0);
                                                                        v_isSharedCheck_4556_ = (!leanh::lean_is_exclusive(v___x_4537_)) as u8;
                                                                        if v_isSharedCheck_4556_
                                                                            == 0
                                                                        {
                                                                            v___x_4551_ =
                                                                                v___x_4537_;
                                                                            v_isShared_4552_ = v_isSharedCheck_4556_;
                                                                            state = 2;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_4549_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_4537_,
                                                                            );
                                                                            v___x_4551_ = leanh::lean_box(0);
                                                                            v_isShared_4552_ = v_isSharedCheck_4556_;
                                                                            state = 2;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_4531_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_4530_,
                                                                );
                                                                leanh::lean_inc_ref(
                                                                    v_arg_4526_,
                                                                );
                                                                v___x_4557_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4526_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_4557_,
                                                                ) == 0
                                                                {
                                                                    v_a_4558_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_4557_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4613_ = (!leanh::lean_is_exclusive(v___x_4557_)) as u8;
                                                                    if v_isSharedCheck_4613_ == 0 {
                                                                        v___x_4560_ = v___x_4557_;
                                                                        v_isShared_4561_ =
                                                                            v_isSharedCheck_4613_;
                                                                        state = 4;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_4558_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_4557_,
                                                                        );
                                                                        v___x_4560_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_4561_ =
                                                                            v_isSharedCheck_4613_;
                                                                        state = 4;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_4526_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_4518_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_4512_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_origExpr_4490_,
                                                                    );
                                                                    return v___x_4557_;
                                                                }
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_4519_);
                                                    v___x_4614_ = 0;
                                                    v___x_4615_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_4518_, v_arg_4512_, v___x_4614_, v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                    return v___x_4615_;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_4519_);
                                                v___x_4616_ = 1;
                                                v___x_4617_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_4518_, v_arg_4512_, v___x_4616_, v_origExpr_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                                return v___x_4617_;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_4513_);
                                        leanh::lean_inc_ref(v_arg_4512_);
                                        v___x_4618_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4512_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                                        if leanh::lean_obj_tag(v___x_4618_) == 0 {
                                            v_a_4619_ = leanh::lean_ctor_get(v___x_4618_, 0);
                                            v_isSharedCheck_4652_ =
                                                (!leanh::lean_is_exclusive(v___x_4618_))
                                                    as u8;
                                            if v_isSharedCheck_4652_ == 0 {
                                                v___x_4621_ = v___x_4618_;
                                                v_isShared_4622_ = v_isSharedCheck_4652_;
                                                state = 16;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4619_);
                                                leanh::lean_dec(v___x_4618_);
                                                v___x_4621_ = leanh::lean_box(0);
                                                v_isShared_4622_ = v_isSharedCheck_4652_;
                                                state = 16;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_4512_);
                                            leanh::lean_dec_ref(v_origExpr_4490_);
                                            return v___x_4618_;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4505_);
                                leanh::lean_dec_ref(v_origExpr_4490_);
                                v___x_4653_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v___x_4509_);
                                if leanh::lean_obj_tag(v___x_4653_) == 0 {
                                    v_a_4654_ = leanh::lean_ctor_get(v___x_4653_, 0);
                                    v_isSharedCheck_4662_ =
                                        (!leanh::lean_is_exclusive(v___x_4653_)) as u8;
                                    if v_isSharedCheck_4662_ == 0 {
                                        v___x_4656_ = v___x_4653_;
                                        v_isShared_4657_ = v_isSharedCheck_4662_;
                                        state = 24;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4654_);
                                        leanh::lean_dec(v___x_4653_);
                                        v___x_4656_ = leanh::lean_box(0);
                                        v_isShared_4657_ = v_isSharedCheck_4662_;
                                        state = 24;
                                        continue;
                                    }
                                } else {
                                    v_a_4663_ = leanh::lean_ctor_get(v___x_4653_, 0);
                                    v_isSharedCheck_4670_ =
                                        (!leanh::lean_is_exclusive(v___x_4653_)) as u8;
                                    if v_isSharedCheck_4670_ == 0 {
                                        v___x_4665_ = v___x_4653_;
                                        v_isShared_4666_ = v_isSharedCheck_4670_;
                                        state = 26;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4663_);
                                        leanh::lean_dec(v___x_4653_);
                                        v___x_4665_ = leanh::lean_box(0);
                                        v_isShared_4666_ = v_isSharedCheck_4670_;
                                        state = 26;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_4505_);
                            leanh::lean_dec_ref(v_origExpr_4490_);
                            v___x_4671_ = 0;
                            v___x_4672_ =
                                l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(
                                    v___x_4671_,
                                );
                            if leanh::lean_obj_tag(v___x_4672_) == 0 {
                                v_a_4673_ = leanh::lean_ctor_get(v___x_4672_, 0);
                                v_isSharedCheck_4681_ =
                                    (!leanh::lean_is_exclusive(v___x_4672_)) as u8;
                                if v_isSharedCheck_4681_ == 0 {
                                    v___x_4675_ = v___x_4672_;
                                    v_isShared_4676_ = v_isSharedCheck_4681_;
                                    state = 28;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4673_);
                                    leanh::lean_dec(v___x_4672_);
                                    v___x_4675_ = leanh::lean_box(0);
                                    v_isShared_4676_ = v_isSharedCheck_4681_;
                                    state = 28;
                                    continue;
                                }
                            } else {
                                v_a_4682_ = leanh::lean_ctor_get(v___x_4672_, 0);
                                v_isSharedCheck_4689_ =
                                    (!leanh::lean_is_exclusive(v___x_4672_)) as u8;
                                if v_isSharedCheck_4689_ == 0 {
                                    v___x_4684_ = v___x_4672_;
                                    v_isShared_4685_ = v_isSharedCheck_4689_;
                                    state = 30;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4682_);
                                    leanh::lean_dec(v___x_4672_);
                                    v___x_4684_ = leanh::lean_box(0);
                                    v_isShared_4685_ = v_isSharedCheck_4689_;
                                    state = 30;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_origExpr_4490_);
                        v_a_4690_ = leanh::lean_ctor_get(v___x_4503_, 0);
                        v_isSharedCheck_4697_ =
                            (!leanh::lean_is_exclusive(v___x_4503_)) as u8;
                        if v_isSharedCheck_4697_ == 0 {
                            v___x_4692_ = v___x_4503_;
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 32;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4690_);
                            leanh::lean_dec(v___x_4503_);
                            v___x_4692_ = leanh::lean_box(0);
                            v_isShared_4693_ = v_isSharedCheck_4697_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4490_);
                    v_a_4698_ = leanh::lean_ctor_get(v___x_4502_, 0);
                    v_isSharedCheck_4705_ = (!leanh::lean_is_exclusive(v___x_4502_)) as u8;
                    if v_isSharedCheck_4705_ == 0 {
                        v___x_4700_ = v___x_4502_;
                        v_isShared_4701_ = v_isSharedCheck_4705_;
                        state = 34;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4698_);
                        leanh::lean_dec(v___x_4502_);
                        v___x_4700_ = leanh::lean_box(0);
                        v_isShared_4701_ = v_isSharedCheck_4705_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4499_ = leanh::lean_box(0);
                v___x_4500_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4500_, 0, v___x_4499_);
                return v___x_4500_;
            }
            2 => {
                if v_isShared_4552_ == 0 {
                    v___x_4554_ = v___x_4551_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4555_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
                    v___x_4554_ = v_reuseFailAlloc_4555_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4554_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_4558_) == 1 {
                    leanh::lean_del_object(v___x_4560_);
                    v_val_4562_ = leanh::lean_ctor_get(v_a_4558_, 0);
                    leanh::lean_inc(v_val_4562_);
                    leanh::lean_dec_ref_known(v_a_4558_, 1);
                    leanh::lean_inc_ref(v_arg_4518_);
                    v___x_4563_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4518_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                    if leanh::lean_obj_tag(v___x_4563_) == 0 {
                        v_a_4564_ = leanh::lean_ctor_get(v___x_4563_, 0);
                        v_isSharedCheck_4608_ =
                            (!leanh::lean_is_exclusive(v___x_4563_)) as u8;
                        if v_isSharedCheck_4608_ == 0 {
                            v___x_4566_ = v___x_4563_;
                            v_isShared_4567_ = v_isSharedCheck_4608_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4564_);
                            leanh::lean_dec(v___x_4563_);
                            v___x_4566_ = leanh::lean_box(0);
                            v_isShared_4567_ = v_isSharedCheck_4608_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4562_);
                        leanh::lean_dec_ref(v_arg_4526_);
                        leanh::lean_dec_ref(v_arg_4518_);
                        leanh::lean_dec_ref(v_arg_4512_);
                        leanh::lean_dec_ref(v_origExpr_4490_);
                        return v___x_4563_;
                    }
                } else {
                    leanh::lean_dec(v_a_4558_);
                    leanh::lean_dec_ref(v_arg_4526_);
                    leanh::lean_dec_ref(v_arg_4518_);
                    leanh::lean_dec_ref(v_arg_4512_);
                    leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4609_ = leanh::lean_box(0);
                    if v_isShared_4561_ == 0 {
                        leanh::lean_ctor_set(v___x_4560_, 0, v___x_4609_);
                        v___x_4611_ = v___x_4560_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
                        v___x_4611_ = v_reuseFailAlloc_4612_;
                        state = 15;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_4564_) == 1 {
                    leanh::lean_del_object(v___x_4566_);
                    v_val_4568_ = leanh::lean_ctor_get(v_a_4564_, 0);
                    leanh::lean_inc(v_val_4568_);
                    leanh::lean_dec_ref_known(v_a_4564_, 1);
                    leanh::lean_inc_ref(v_arg_4512_);
                    v___x_4569_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_4512_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_, v_a_4496_);
                    if leanh::lean_obj_tag(v___x_4569_) == 0 {
                        v_a_4570_ = leanh::lean_ctor_get(v___x_4569_, 0);
                        v_isSharedCheck_4603_ =
                            (!leanh::lean_is_exclusive(v___x_4569_)) as u8;
                        if v_isSharedCheck_4603_ == 0 {
                            v___x_4572_ = v___x_4569_;
                            v_isShared_4573_ = v_isSharedCheck_4603_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4570_);
                            leanh::lean_dec(v___x_4569_);
                            v___x_4572_ = leanh::lean_box(0);
                            v_isShared_4573_ = v_isSharedCheck_4603_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_4568_);
                        leanh::lean_dec(v_val_4562_);
                        leanh::lean_dec_ref(v_arg_4526_);
                        leanh::lean_dec_ref(v_arg_4518_);
                        leanh::lean_dec_ref(v_arg_4512_);
                        leanh::lean_dec_ref(v_origExpr_4490_);
                        return v___x_4569_;
                    }
                } else {
                    leanh::lean_dec(v_a_4564_);
                    leanh::lean_dec(v_val_4562_);
                    leanh::lean_dec_ref(v_arg_4526_);
                    leanh::lean_dec_ref(v_arg_4518_);
                    leanh::lean_dec_ref(v_arg_4512_);
                    leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4604_ = leanh::lean_box(0);
                    if v_isShared_4567_ == 0 {
                        leanh::lean_ctor_set(v___x_4566_, 0, v___x_4604_);
                        v___x_4606_ = v___x_4566_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4607_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
                        v___x_4606_ = v_reuseFailAlloc_4607_;
                        state = 14;
                        continue;
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_a_4570_) == 1 {
                    leanh::lean_del_object(v___x_4572_);
                    v_val_4574_ = leanh::lean_ctor_get(v_a_4570_, 0);
                    v_isSharedCheck_4598_ = (!leanh::lean_is_exclusive(v_a_4570_)) as u8;
                    if v_isSharedCheck_4598_ == 0 {
                        v___x_4576_ = v_a_4570_;
                        v_isShared_4577_ = v_isSharedCheck_4598_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4574_);
                        leanh::lean_dec(v_a_4570_);
                        v___x_4576_ = leanh::lean_box(0);
                        v_isShared_4577_ = v_isSharedCheck_4598_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4570_);
                    leanh::lean_dec(v_val_4568_);
                    leanh::lean_dec(v_val_4562_);
                    leanh::lean_dec_ref(v_arg_4526_);
                    leanh::lean_dec_ref(v_arg_4518_);
                    leanh::lean_dec_ref(v_arg_4512_);
                    leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4599_ = leanh::lean_box(0);
                    if v_isShared_4573_ == 0 {
                        leanh::lean_ctor_set(v___x_4572_, 0, v___x_4599_);
                        v___x_4601_ = v___x_4572_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
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
                if leanh::lean_obj_tag(v___x_4578_) == 0 {
                    v_a_4579_ = leanh::lean_ctor_get(v___x_4578_, 0);
                    v_isSharedCheck_4589_ = (!leanh::lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4589_ == 0 {
                        v___x_4581_ = v___x_4578_;
                        v_isShared_4582_ = v_isSharedCheck_4589_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4579_);
                        leanh::lean_dec(v___x_4578_);
                        v___x_4581_ = leanh::lean_box(0);
                        v_isShared_4582_ = v_isSharedCheck_4589_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4576_);
                    v_a_4590_ = leanh::lean_ctor_get(v___x_4578_, 0);
                    v_isSharedCheck_4597_ = (!leanh::lean_is_exclusive(v___x_4578_)) as u8;
                    if v_isSharedCheck_4597_ == 0 {
                        v___x_4592_ = v___x_4578_;
                        v_isShared_4593_ = v_isSharedCheck_4597_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4590_);
                        leanh::lean_dec(v___x_4578_);
                        v___x_4592_ = leanh::lean_box(0);
                        v_isShared_4593_ = v_isSharedCheck_4597_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4577_ == 0 {
                    leanh::lean_ctor_set(v___x_4576_, 0, v_a_4579_);
                    v___x_4584_ = v___x_4576_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4588_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4588_, 0, v_a_4579_);
                    v___x_4584_ = v_reuseFailAlloc_4588_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4582_ == 0 {
                    leanh::lean_ctor_set(v___x_4581_, 0, v___x_4584_);
                    v___x_4586_ = v___x_4581_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 0, v___x_4584_);
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
                    v_reuseFailAlloc_4596_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_a_4590_);
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
                if leanh::lean_obj_tag(v_a_4619_) == 1 {
                    leanh::lean_del_object(v___x_4621_);
                    v_val_4623_ = leanh::lean_ctor_get(v_a_4619_, 0);
                    v_isSharedCheck_4647_ = (!leanh::lean_is_exclusive(v_a_4619_)) as u8;
                    if v_isSharedCheck_4647_ == 0 {
                        v___x_4625_ = v_a_4619_;
                        v_isShared_4626_ = v_isSharedCheck_4647_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4623_);
                        leanh::lean_dec(v_a_4619_);
                        v___x_4625_ = leanh::lean_box(0);
                        v_isShared_4626_ = v_isSharedCheck_4647_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4619_);
                    leanh::lean_dec_ref(v_arg_4512_);
                    leanh::lean_dec_ref(v_origExpr_4490_);
                    v___x_4648_ = leanh::lean_box(0);
                    if v_isShared_4622_ == 0 {
                        leanh::lean_ctor_set(v___x_4621_, 0, v___x_4648_);
                        v___x_4650_ = v___x_4621_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_4651_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 0, v___x_4648_);
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
                if leanh::lean_obj_tag(v___x_4627_) == 0 {
                    v_a_4628_ = leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4638_ = (!leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4638_ == 0 {
                        v___x_4630_ = v___x_4627_;
                        v_isShared_4631_ = v_isSharedCheck_4638_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4628_);
                        leanh::lean_dec(v___x_4627_);
                        v___x_4630_ = leanh::lean_box(0);
                        v_isShared_4631_ = v_isSharedCheck_4638_;
                        state = 18;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4625_);
                    v_a_4639_ = leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4646_ = (!leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4646_ == 0 {
                        v___x_4641_ = v___x_4627_;
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4639_);
                        leanh::lean_dec(v___x_4627_);
                        v___x_4641_ = leanh::lean_box(0);
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4626_ == 0 {
                    leanh::lean_ctor_set(v___x_4625_, 0, v_a_4628_);
                    v___x_4633_ = v___x_4625_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4637_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4628_);
                    v___x_4633_ = v_reuseFailAlloc_4637_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4631_ == 0 {
                    leanh::lean_ctor_set(v___x_4630_, 0, v___x_4633_);
                    v___x_4635_ = v___x_4630_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v___x_4633_);
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
                    v_reuseFailAlloc_4645_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
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
                v___x_4658_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4658_, 0, v_a_4654_);
                if v_isShared_4657_ == 0 {
                    leanh::lean_ctor_set(v___x_4656_, 0, v___x_4658_);
                    v___x_4660_ = v___x_4656_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4661_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v___x_4658_);
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
                    v_reuseFailAlloc_4669_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
                    v___x_4668_ = v_reuseFailAlloc_4669_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4668_;
            }
            28 => {
                v___x_4677_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4677_, 0, v_a_4673_);
                if v_isShared_4676_ == 0 {
                    leanh::lean_ctor_set(v___x_4675_, 0, v___x_4677_);
                    v___x_4679_ = v___x_4675_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4680_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4680_, 0, v___x_4677_);
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
                    v_reuseFailAlloc_4688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
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
                    v_reuseFailAlloc_4696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4696_, 0, v_a_4690_);
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
                    v_reuseFailAlloc_4704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_a_4698_);
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
    mut v_e_4706_: *mut leanh::LeanObject,
    mut v_a_4707_: *mut leanh::LeanObject,
    mut v_a_4708_: *mut leanh::LeanObject,
    mut v_a_4709_: *mut leanh::LeanObject,
    mut v_a_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4719_: u8 = 0;
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4738_ = lean_st_ref_get(v_a_4707_);
                v_bvLogicalCache_4739_ = leanh::lean_ctor_get(v___x_4738_, 3);
                leanh::lean_inc_ref(v_bvLogicalCache_4739_);
                leanh::lean_dec(v___x_4738_);
                v___x_4740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvLogicalCache_4739_, v_e_4706_);
                leanh::lean_dec_ref(v_bvLogicalCache_4739_);
                if leanh::lean_obj_tag(v___x_4740_) == 0 {
                    leanh::lean_inc_ref(v_e_4706_);
                    v___x_4741_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_e_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_);
                    if leanh::lean_obj_tag(v___x_4741_) == 0 {
                        v_a_4742_ = leanh::lean_ctor_get(v___x_4741_, 0);
                        leanh::lean_inc(v_a_4742_);
                        if leanh::lean_obj_tag(v_a_4742_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4741_, 1);
                            leanh::lean_inc_ref(v_e_4706_);
                            v___x_4743_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(
                                v_e_4706_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_,
                            );
                            v___y_4715_ = v___x_4743_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v_a_4742_, 1);
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
                    leanh::lean_dec_ref(v_e_4706_);
                    v_val_4744_ = leanh::lean_ctor_get(v___x_4740_, 0);
                    v_isSharedCheck_4751_ = (!leanh::lean_is_exclusive(v___x_4740_)) as u8;
                    if v_isSharedCheck_4751_ == 0 {
                        v___x_4746_ = v___x_4740_;
                        v_isShared_4747_ = v_isSharedCheck_4751_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4744_);
                        leanh::lean_dec(v___x_4740_);
                        v___x_4746_ = leanh::lean_box(0);
                        v_isShared_4747_ = v_isSharedCheck_4751_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4715_) == 0 {
                    v_a_4716_ = leanh::lean_ctor_get(v___y_4715_, 0);
                    v_isSharedCheck_4737_ = (!leanh::lean_is_exclusive(v___y_4715_)) as u8;
                    if v_isSharedCheck_4737_ == 0 {
                        v___x_4718_ = v___y_4715_;
                        v_isShared_4719_ = v_isSharedCheck_4737_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4716_);
                        leanh::lean_dec(v___y_4715_);
                        v___x_4718_ = leanh::lean_box(0);
                        v_isShared_4719_ = v_isSharedCheck_4737_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4706_);
                    return v___y_4715_;
                }
            }
            2 => {
                v___x_4720_ = lean_st_ref_take(v_a_4707_);
                v_lemmas_4721_ = leanh::lean_ctor_get(v___x_4720_, 0);
                v_bvExprCache_4722_ = leanh::lean_ctor_get(v___x_4720_, 1);
                v_bvPredCache_4723_ = leanh::lean_ctor_get(v___x_4720_, 2);
                v_bvLogicalCache_4724_ = leanh::lean_ctor_get(v___x_4720_, 3);
                v_isSharedCheck_4736_ = (!leanh::lean_is_exclusive(v___x_4720_)) as u8;
                if v_isSharedCheck_4736_ == 0 {
                    v___x_4726_ = v___x_4720_;
                    v_isShared_4727_ = v_isSharedCheck_4736_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_bvLogicalCache_4724_);
                    leanh::lean_inc(v_bvPredCache_4723_);
                    leanh::lean_inc(v_bvExprCache_4722_);
                    leanh::lean_inc(v_lemmas_4721_);
                    leanh::lean_dec(v___x_4720_);
                    v___x_4726_ = leanh::lean_box(0);
                    v_isShared_4727_ = v_isSharedCheck_4736_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_4716_);
                v___x_4728_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvLogicalCache_4724_, v_e_4706_, v_a_4716_);
                if v_isShared_4727_ == 0 {
                    leanh::lean_ctor_set(v___x_4726_, 3, v___x_4728_);
                    v___x_4730_ = v___x_4726_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_lemmas_4721_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 1, v_bvExprCache_4722_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 2, v_bvPredCache_4723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 3, v___x_4728_);
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
                    v_reuseFailAlloc_4734_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4716_);
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
                    leanh::lean_ctor_set_tag(v___x_4746_, 0);
                    v___x_4749_ = v___x_4746_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_val_4744_);
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
    mut v_origExpr_4752_: *mut leanh::LeanObject,
    mut v_a_4753_: *mut leanh::LeanObject,
    mut v_a_4754_: *mut leanh::LeanObject,
    mut v_a_4755_: *mut leanh::LeanObject,
    mut v_a_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
    mut v_a_4758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4760_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_origExpr_4752_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
    return v___x_4760_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(
    mut v_origExpr_4761_: *mut leanh::LeanObject,
    mut v_a_4762_: *mut leanh::LeanObject,
    mut v_a_4763_: *mut leanh::LeanObject,
    mut v_a_4764_: *mut leanh::LeanObject,
    mut v_a_4765_: *mut leanh::LeanObject,
    mut v_a_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4769_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
    return v___x_4769_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4785_ = leanh::lean_box(0);
    v___x_4786_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5;
    v___x_4787_ = l_Lean_mkConst(v___x_4786_, v___x_4785_);
    return v___x_4787_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4795_ = leanh::lean_box(0);
    v___x_4796_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2;
    v___x_4797_ = l_Lean_mkConst(v___x_4796_, v___x_4795_);
    return v___x_4797_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4804_ = leanh::lean_box(0);
    v___x_4805_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5;
    v___x_4806_ = l_Lean_mkConst(v___x_4805_, v___x_4804_);
    return v___x_4806_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4813_ = leanh::lean_box(0);
    v___x_4814_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8;
    v___x_4815_ = l_Lean_mkConst(v___x_4814_, v___x_4813_);
    return v___x_4815_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4823_ = leanh::lean_box(0);
    v___x_4824_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11;
    v___x_4825_ = l_Lean_mkConst(v___x_4824_, v___x_4823_);
    return v___x_4825_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = leanh::lean_box(0);
    v___x_4833_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14;
    v___x_4834_ = l_Lean_mkConst(v___x_4833_, v___x_4832_);
    return v___x_4834_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4841_ = leanh::lean_box(0);
    v___x_4842_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17;
    v___x_4843_ = l_Lean_mkConst(v___x_4842_, v___x_4841_);
    return v___x_4843_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4850_ = leanh::lean_box(0);
    v___x_4851_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20;
    v___x_4852_ = l_Lean_mkConst(v___x_4851_, v___x_4850_);
    return v___x_4852_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(
    mut v_innerExpr_4853_: *mut leanh::LeanObject,
    mut v_op_4854_: *mut leanh::LeanObject,
    mut v_congrThm_4855_: *mut leanh::LeanObject,
    mut v_origExpr_4856_: *mut leanh::LeanObject,
    mut v_a_4857_: *mut leanh::LeanObject,
    mut v_a_4858_: *mut leanh::LeanObject,
    mut v_a_4859_: *mut leanh::LeanObject,
    mut v_a_4860_: *mut leanh::LeanObject,
    mut v_a_4861_: *mut leanh::LeanObject,
    mut v_a_4862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v_val_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4872_: u8 = 0;
    let mut v_width_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4908_: u8 = 0;
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_innerExpr_4853_);
                v___x_4864_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4853_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_, v_a_4861_, v_a_4862_);
                if leanh::lean_obj_tag(v___x_4864_) == 0 {
                    v_a_4865_ = leanh::lean_ctor_get(v___x_4864_, 0);
                    v_isSharedCheck_4913_ = (!leanh::lean_is_exclusive(v___x_4864_)) as u8;
                    if v_isSharedCheck_4913_ == 0 {
                        v___x_4867_ = v___x_4864_;
                        v_isShared_4868_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4865_);
                        leanh::lean_dec(v___x_4864_);
                        v___x_4867_ = leanh::lean_box(0);
                        v_isShared_4868_ = v_isSharedCheck_4913_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4856_);
                    leanh::lean_dec(v_congrThm_4855_);
                    leanh::lean_dec(v_op_4854_);
                    leanh::lean_dec_ref(v_innerExpr_4853_);
                    return v___x_4864_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4865_) == 1 {
                    v_val_4869_ = leanh::lean_ctor_get(v_a_4865_, 0);
                    v_isSharedCheck_4908_ = (!leanh::lean_is_exclusive(v_a_4865_)) as u8;
                    if v_isSharedCheck_4908_ == 0 {
                        v___x_4871_ = v_a_4865_;
                        v_isShared_4872_ = v_isSharedCheck_4908_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4869_);
                        leanh::lean_dec(v_a_4865_);
                        v___x_4871_ = leanh::lean_box(0);
                        v_isShared_4872_ = v_isSharedCheck_4908_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4865_);
                    leanh::lean_dec_ref(v_origExpr_4856_);
                    leanh::lean_dec(v_congrThm_4855_);
                    leanh::lean_dec(v_op_4854_);
                    leanh::lean_dec_ref(v_innerExpr_4853_);
                    v___x_4909_ = leanh::lean_box(0);
                    if v_isShared_4868_ == 0 {
                        leanh::lean_ctor_set(v___x_4867_, 0, v___x_4909_);
                        v___x_4911_ = v___x_4867_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
                        v___x_4911_ = v_reuseFailAlloc_4912_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_width_4873_ = leanh::lean_ctor_get(v_val_4869_, 0);
                leanh::lean_inc_n(v_width_4873_, 3);
                v_bvExpr_4874_ = leanh::lean_ctor_get(v_val_4869_, 1);
                v_expr_4875_ = leanh::lean_ctor_get(v_val_4869_, 4);
                leanh::lean_inc_ref(v_bvExpr_4874_);
                leanh::lean_inc(v_op_4854_);
                v___x_4876_ = l_Std_Tactic_BVDecide_BVExpr_un___override(
                    v_width_4873_,
                    v_op_4854_,
                    v_bvExpr_4874_,
                );
                v___x_4877_ = leanh::lean_box(0);
                v___x_4878_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
                v___x_4879_ = l_Lean_mkNatLit(v_width_4873_);
                match leanh::lean_obj_tag(v_op_4854_) {
                    0 => {
                        v___x_4892_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3);
                        v___y_4881_ = v___x_4892_;
                        state = 3;
                        continue;
                    }
                    1 => {
                        v_n_4893_ = leanh::lean_ctor_get(v_op_4854_, 0);
                        leanh::lean_inc(v_n_4893_);
                        leanh::lean_dec_ref_known(v_op_4854_, 1);
                        v___x_4894_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6);
                        v___x_4895_ = l_Lean_mkNatLit(v_n_4893_);
                        v___x_4896_ = l_Lean_Expr_app___override(v___x_4894_, v___x_4895_);
                        v___y_4881_ = v___x_4896_;
                        state = 3;
                        continue;
                    }
                    2 => {
                        v_n_4897_ = leanh::lean_ctor_get(v_op_4854_, 0);
                        leanh::lean_inc(v_n_4897_);
                        leanh::lean_dec_ref_known(v_op_4854_, 1);
                        v___x_4898_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9);
                        v___x_4899_ = l_Lean_mkNatLit(v_n_4897_);
                        v___x_4900_ = l_Lean_Expr_app___override(v___x_4898_, v___x_4899_);
                        v___y_4881_ = v___x_4900_;
                        state = 3;
                        continue;
                    }
                    3 => {
                        v_n_4901_ = leanh::lean_ctor_get(v_op_4854_, 0);
                        leanh::lean_inc(v_n_4901_);
                        leanh::lean_dec_ref_known(v_op_4854_, 1);
                        v___x_4902_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12);
                        v___x_4903_ = l_Lean_mkNatLit(v_n_4901_);
                        v___x_4904_ = l_Lean_Expr_app___override(v___x_4902_, v___x_4903_);
                        v___y_4881_ = v___x_4904_;
                        state = 3;
                        continue;
                    }
                    4 => {
                        v___x_4905_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15);
                        v___y_4881_ = v___x_4905_;
                        state = 3;
                        continue;
                    }
                    5 => {
                        v___x_4906_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18);
                        v___y_4881_ = v___x_4906_;
                        state = 3;
                        continue;
                    }
                    _ => {
                        v___x_4907_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21);
                        v___y_4881_ = v___x_4907_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc_ref(v_expr_4875_);
                v___x_4882_ = l_Lean_mkApp3(v___x_4878_, v___x_4879_, v___y_4881_, v_expr_4875_);
                v___x_4883_ = l_Lean_mkConst(v_congrThm_4855_, v___x_4877_);
                v___x_4884_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed as *mut core::ffi::c_void, 9, 3);
                leanh::lean_closure_set(v___x_4884_, 0, v_val_4869_);
                leanh::lean_closure_set(v___x_4884_, 1, v_innerExpr_4853_);
                leanh::lean_closure_set(v___x_4884_, 2, v___x_4883_);
                v___x_4885_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4885_, 0, v_width_4873_);
                leanh::lean_ctor_set(v___x_4885_, 1, v___x_4876_);
                leanh::lean_ctor_set(v___x_4885_, 2, v_origExpr_4856_);
                leanh::lean_ctor_set(v___x_4885_, 3, v___x_4884_);
                leanh::lean_ctor_set(v___x_4885_, 4, v___x_4882_);
                if v_isShared_4872_ == 0 {
                    leanh::lean_ctor_set(v___x_4871_, 0, v___x_4885_);
                    v___x_4887_ = v___x_4871_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4891_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4891_, 0, v___x_4885_);
                    v___x_4887_ = v_reuseFailAlloc_4891_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4868_ == 0 {
                    leanh::lean_ctor_set(v___x_4867_, 0, v___x_4887_);
                    v___x_4889_ = v___x_4867_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4890_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
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
    mut v_distance_4923_: *mut leanh::LeanObject,
    mut v_innerExpr_4924_: *mut leanh::LeanObject,
    mut v_shiftOp_4925_: *mut leanh::LeanObject,
    mut v_shiftOpName_4926_: *mut leanh::LeanObject,
    mut v_congrThm_4927_: *mut leanh::LeanObject,
    mut v_origExpr_4928_: *mut leanh::LeanObject,
    mut v_a_4929_: *mut leanh::LeanObject,
    mut v_a_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
    mut v_a_4934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4940_: u8 = 0;
    let mut v_val_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v_width_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_innerExpr_4924_);
                v___x_4936_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_4924_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_);
                if leanh::lean_obj_tag(v___x_4936_) == 0 {
                    v_a_4937_ = leanh::lean_ctor_get(v___x_4936_, 0);
                    v_isSharedCheck_4972_ = (!leanh::lean_is_exclusive(v___x_4936_)) as u8;
                    if v_isSharedCheck_4972_ == 0 {
                        v___x_4939_ = v___x_4936_;
                        v_isShared_4940_ = v_isSharedCheck_4972_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4937_);
                        leanh::lean_dec(v___x_4936_);
                        v___x_4939_ = leanh::lean_box(0);
                        v_isShared_4940_ = v_isSharedCheck_4972_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4928_);
                    leanh::lean_dec(v_congrThm_4927_);
                    leanh::lean_dec(v_shiftOpName_4926_);
                    leanh::lean_dec_ref(v_shiftOp_4925_);
                    leanh::lean_dec_ref(v_innerExpr_4924_);
                    leanh::lean_dec(v_distance_4923_);
                    return v___x_4936_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4937_) == 1 {
                    v_val_4941_ = leanh::lean_ctor_get(v_a_4937_, 0);
                    v_isSharedCheck_4967_ = (!leanh::lean_is_exclusive(v_a_4937_)) as u8;
                    if v_isSharedCheck_4967_ == 0 {
                        v___x_4943_ = v_a_4937_;
                        v_isShared_4944_ = v_isSharedCheck_4967_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4941_);
                        leanh::lean_dec(v_a_4937_);
                        v___x_4943_ = leanh::lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4967_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4937_);
                    leanh::lean_dec_ref(v_origExpr_4928_);
                    leanh::lean_dec(v_congrThm_4927_);
                    leanh::lean_dec(v_shiftOpName_4926_);
                    leanh::lean_dec_ref(v_shiftOp_4925_);
                    leanh::lean_dec_ref(v_innerExpr_4924_);
                    leanh::lean_dec(v_distance_4923_);
                    v___x_4968_ = leanh::lean_box(0);
                    if v_isShared_4940_ == 0 {
                        leanh::lean_ctor_set(v___x_4939_, 0, v___x_4968_);
                        v___x_4970_ = v___x_4939_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4971_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4968_);
                        v___x_4970_ = v_reuseFailAlloc_4971_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_width_4945_ = leanh::lean_ctor_get(v_val_4941_, 0);
                leanh::lean_inc_n(v_width_4945_, 3);
                v_bvExpr_4946_ = leanh::lean_ctor_get(v_val_4941_, 1);
                v_expr_4947_ = leanh::lean_ctor_get(v_val_4941_, 4);
                leanh::lean_inc(v_distance_4923_);
                v___x_4948_ = leanh::lean_apply_1(v_shiftOp_4925_, v_distance_4923_);
                leanh::lean_inc_ref(v_bvExpr_4946_);
                v___x_4949_ = l_Std_Tactic_BVDecide_BVExpr_un___override(
                    v_width_4945_,
                    v___x_4948_,
                    v_bvExpr_4946_,
                );
                v___x_4950_ = leanh::lean_box(0);
                v___x_4951_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
                v___x_4952_ = l_Lean_mkNatLit(v_width_4945_);
                v___x_4953_ = l_Lean_mkConst(v_shiftOpName_4926_, v___x_4950_);
                v___x_4954_ = l_Lean_mkNatLit(v_distance_4923_);
                leanh::lean_inc_ref(v___x_4954_);
                v___x_4955_ = l_Lean_Expr_app___override(v___x_4953_, v___x_4954_);
                leanh::lean_inc_ref(v_expr_4947_);
                v___x_4956_ = l_Lean_mkApp3(v___x_4951_, v___x_4952_, v___x_4955_, v_expr_4947_);
                v___x_4957_ = l_Lean_mkConst(v_congrThm_4927_, v___x_4950_);
                v___x_4958_ = l_Lean_Expr_app___override(v___x_4957_, v___x_4954_);
                v___x_4959_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed as *mut core::ffi::c_void, 9, 3);
                leanh::lean_closure_set(v___x_4959_, 0, v_val_4941_);
                leanh::lean_closure_set(v___x_4959_, 1, v_innerExpr_4924_);
                leanh::lean_closure_set(v___x_4959_, 2, v___x_4958_);
                v___x_4960_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4960_, 0, v_width_4945_);
                leanh::lean_ctor_set(v___x_4960_, 1, v___x_4949_);
                leanh::lean_ctor_set(v___x_4960_, 2, v_origExpr_4928_);
                leanh::lean_ctor_set(v___x_4960_, 3, v___x_4959_);
                leanh::lean_ctor_set(v___x_4960_, 4, v___x_4956_);
                if v_isShared_4944_ == 0 {
                    leanh::lean_ctor_set(v___x_4943_, 0, v___x_4960_);
                    v___x_4962_ = v___x_4943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4960_);
                    v___x_4962_ = v_reuseFailAlloc_4966_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4940_ == 0 {
                    leanh::lean_ctor_set(v___x_4939_, 0, v___x_4962_);
                    v___x_4964_ = v___x_4939_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4962_);
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
-> *mut leanh::LeanObject {
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4979_ = leanh::lean_box(0);
    v___x_4980_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85;
    v___x_4981_ = l_Lean_mkConst(v___x_4980_, v___x_4979_);
    return v___x_4981_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(
    mut v_distanceExpr_4991_: *mut leanh::LeanObject,
    mut v_innerExpr_4992_: *mut leanh::LeanObject,
    mut v_rotateOp_4993_: *mut leanh::LeanObject,
    mut v_rotateOpName_4994_: *mut leanh::LeanObject,
    mut v_congrThm_4995_: *mut leanh::LeanObject,
    mut v_origExpr_4996_: *mut leanh::LeanObject,
    mut v_a_4997_: *mut leanh::LeanObject,
    mut v_a_4998_: *mut leanh::LeanObject,
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_a_5000_: *mut leanh::LeanObject,
    mut v_a_5001_: *mut leanh::LeanObject,
    mut v_a_5002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v_val_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_a_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_5004_) == 0 {
                    v_a_5005_ = leanh::lean_ctor_get(v___x_5004_, 0);
                    v_isSharedCheck_5015_ = (!leanh::lean_is_exclusive(v___x_5004_)) as u8;
                    if v_isSharedCheck_5015_ == 0 {
                        v___x_5007_ = v___x_5004_;
                        v_isShared_5008_ = v_isSharedCheck_5015_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5005_);
                        leanh::lean_dec(v___x_5004_);
                        v___x_5007_ = leanh::lean_box(0);
                        v_isShared_5008_ = v_isSharedCheck_5015_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_4996_);
                    leanh::lean_dec(v_congrThm_4995_);
                    leanh::lean_dec(v_rotateOpName_4994_);
                    leanh::lean_dec_ref(v_rotateOp_4993_);
                    leanh::lean_dec_ref(v_innerExpr_4992_);
                    v_a_5016_ = leanh::lean_ctor_get(v___x_5004_, 0);
                    v_isSharedCheck_5023_ = (!leanh::lean_is_exclusive(v___x_5004_)) as u8;
                    if v_isSharedCheck_5023_ == 0 {
                        v___x_5018_ = v___x_5004_;
                        v_isShared_5019_ = v_isSharedCheck_5023_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5016_);
                        leanh::lean_dec(v___x_5004_);
                        v___x_5018_ = leanh::lean_box(0);
                        v_isShared_5019_ = v_isSharedCheck_5023_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5005_) == 1 {
                    leanh::lean_del_object(v___x_5007_);
                    v_val_5009_ = leanh::lean_ctor_get(v_a_5005_, 0);
                    leanh::lean_inc(v_val_5009_);
                    leanh::lean_dec_ref_known(v_a_5005_, 1);
                    v___x_5010_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_5009_, v_innerExpr_4992_, v_rotateOp_4993_, v_rotateOpName_4994_, v_congrThm_4995_, v_origExpr_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_);
                    return v___x_5010_;
                } else {
                    leanh::lean_dec(v_a_5005_);
                    leanh::lean_dec_ref(v_origExpr_4996_);
                    leanh::lean_dec(v_congrThm_4995_);
                    leanh::lean_dec(v_rotateOpName_4994_);
                    leanh::lean_dec_ref(v_rotateOp_4993_);
                    leanh::lean_dec_ref(v_innerExpr_4992_);
                    v___x_5011_ = leanh::lean_box(0);
                    if v_isShared_5008_ == 0 {
                        leanh::lean_ctor_set(v___x_5007_, 0, v___x_5011_);
                        v___x_5013_ = v___x_5007_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5014_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5011_);
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
                    v_reuseFailAlloc_5022_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
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
    mut v_origExpr_5057_: *mut leanh::LeanObject,
    mut v_a_5058_: *mut leanh::LeanObject,
    mut v_a_5059_: *mut leanh::LeanObject,
    mut v_a_5060_: *mut leanh::LeanObject,
    mut v_a_5061_: *mut leanh::LeanObject,
    mut v_a_5062_: *mut leanh::LeanObject,
    mut v_a_5063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5077_: u8 = 0;
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: u8 = 0;
    let mut v_arg_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: u8 = 0;
    let mut v_arg_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: u8 = 0;
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: u8 = 0;
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: u8 = 0;
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: u8 = 0;
    let mut v___x_5099_: u8 = 0;
    let mut v_arg_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: u8 = 0;
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: u8 = 0;
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: u8 = 0;
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: u8 = 0;
    let mut v___x_5112_: u8 = 0;
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: u8 = 0;
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: u8 = 0;
    let mut v_arg_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: u8 = 0;
    let mut v_arg_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: u8 = 0;
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: u8 = 0;
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: u8 = 0;
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: u8 = 0;
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: u8 = 0;
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: u8 = 0;
    let mut v___x_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: u8 = 0;
    let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: u8 = 0;
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: u8 = 0;
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: u8 = 0;
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: u8 = 0;
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: u8 = 0;
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5166_: u8 = 0;
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: u8 = 0;
    let mut v_arg_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: u8 = 0;
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: u8 = 0;
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: u8 = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5201_: u8 = 0;
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5205_: u8 = 0;
    let mut v___y_5207_: u8 = 0;
    let mut v_a_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5215_: u8 = 0;
    let mut v_isSharedCheck_5216_: u8 = 0;
    let mut v_a_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5220_: u8 = 0;
    let mut v___x_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5224_: u8 = 0;
    let mut v___x_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: u8 = 0;
    let mut v_arg_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: u8 = 0;
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: u8 = 0;
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: u8 = 0;
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5264_: u8 = 0;
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5268_: u8 = 0;
    let mut v___y_5270_: u8 = 0;
    let mut v_a_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5274_: u8 = 0;
    let mut v___x_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5278_: u8 = 0;
    let mut v_isSharedCheck_5279_: u8 = 0;
    let mut v_a_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5283_: u8 = 0;
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5292_: u8 = 0;
    let mut v_val_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v_val_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5302_: u8 = 0;
    let mut v_width_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_width_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5316_: u8 = 0;
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut v_a_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5337_: u8 = 0;
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5341_: u8 = 0;
    let mut v_isSharedCheck_5342_: u8 = 0;
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5352_: u8 = 0;
    let mut v___f_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v_val_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5367_: u8 = 0;
    let mut v_val_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5373_: u8 = 0;
    let mut v_val_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5377_: u8 = 0;
    let mut v_width_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5397_: u8 = 0;
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5402_: u8 = 0;
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5407_: u8 = 0;
    let mut v_a_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5411_: u8 = 0;
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5415_: u8 = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v_a_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5433_: u8 = 0;
    let mut v_val_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5439_: u8 = 0;
    let mut v_val_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5445_: u8 = 0;
    let mut v_val_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v_val_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5456_: u8 = 0;
    let mut v___x_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5460_: u8 = 0;
    let mut v_unused_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5465_: u8 = 0;
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5469_: u8 = 0;
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5474_: u8 = 0;
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5484_: u8 = 0;
    let mut v_a_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5488_: u8 = 0;
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5492_: u8 = 0;
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5497_: u8 = 0;
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5505_: u8 = 0;
    let mut v_val_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5515_: u8 = 0;
    let mut v_a_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5519_: u8 = 0;
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5523_: u8 = 0;
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v_val_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5534_: u8 = 0;
    let mut v_val_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5538_: u8 = 0;
    let mut v_width_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5549_: u8 = 0;
    let mut v___x_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut v_a_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5570_: u8 = 0;
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5574_: u8 = 0;
    let mut v_isSharedCheck_5575_: u8 = 0;
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_a_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5584_: u8 = 0;
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5593_: u8 = 0;
    let mut v___f_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5612_: u8 = 0;
    let mut v_a_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5616_: u8 = 0;
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5620_: u8 = 0;
    let mut v_a_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5624_: u8 = 0;
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5071_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0;
                v___x_5072_ = l_Lean_Core_checkSystem(v___x_5071_, v_a_5062_, v_a_5063_);
                if leanh::lean_obj_tag(v___x_5072_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5072_, 1);
                    leanh::lean_inc_ref(v_origExpr_5057_);
                    v___x_5073_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_5057_, v_a_5061_);
                    if leanh::lean_obj_tag(v___x_5073_) == 0 {
                        v_a_5074_ = leanh::lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5612_ =
                            (!leanh::lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5612_ == 0 {
                            v___x_5076_ = v___x_5073_;
                            v_isShared_5077_ = v_isSharedCheck_5612_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5074_);
                            leanh::lean_dec(v___x_5073_);
                            v___x_5076_ = leanh::lean_box(0);
                            v_isShared_5077_ = v_isSharedCheck_5612_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5613_ = leanh::lean_ctor_get(v___x_5073_, 0);
                        v_isSharedCheck_5620_ =
                            (!leanh::lean_is_exclusive(v___x_5073_)) as u8;
                        if v_isSharedCheck_5620_ == 0 {
                            v___x_5615_ = v___x_5073_;
                            v_isShared_5616_ = v_isSharedCheck_5620_;
                            state = 83;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5613_);
                            leanh::lean_dec(v___x_5073_);
                            v___x_5615_ = leanh::lean_box(0);
                            v_isShared_5616_ = v_isSharedCheck_5620_;
                            state = 83;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5621_ = leanh::lean_ctor_get(v___x_5072_, 0);
                    v_isSharedCheck_5628_ = (!leanh::lean_is_exclusive(v___x_5072_)) as u8;
                    if v_isSharedCheck_5628_ == 0 {
                        v___x_5623_ = v___x_5072_;
                        v_isShared_5624_ = v_isSharedCheck_5628_;
                        state = 85;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5621_);
                        leanh::lean_dec(v___x_5072_);
                        v___x_5623_ = leanh::lean_box(0);
                        v_isShared_5624_ = v_isSharedCheck_5628_;
                        state = 85;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5066_ = leanh::lean_box(0);
                v___x_5067_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5067_, 0, v___x_5066_);
                return v___x_5067_;
            }
            2 => {
                v___x_5069_ = leanh::lean_box(0);
                v___x_5070_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5070_, 0, v___x_5069_);
                return v___x_5070_;
            }
            3 => {
                v___x_5083_ = l_Lean_Expr_cleanupAnnotations(v_a_5074_);
                v___x_5084_ = l_Lean_Expr_isApp(v___x_5083_);
                if v___x_5084_ == 0 {
                    leanh::lean_dec_ref(v___x_5083_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 4;
                    continue;
                } else {
                    v_arg_5085_ = leanh::lean_ctor_get(v___x_5083_, 1);
                    leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5086_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5083_);
                    v___x_5087_ = l_Lean_Expr_isApp(v___x_5086_);
                    if v___x_5087_ == 0 {
                        leanh::lean_dec_ref(v___x_5086_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 4;
                        continue;
                    } else {
                        v_arg_5088_ = leanh::lean_ctor_get(v___x_5086_, 1);
                        leanh::lean_inc_ref(v_arg_5088_);
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
                                            leanh::lean_dec_ref(v___x_5089_);
                                            leanh::lean_dec_ref(v_arg_5088_);
                                            leanh::lean_dec_ref(v_arg_5085_);
                                            leanh::lean_dec_ref(v_origExpr_5057_);
                                            state = 4;
                                            continue;
                                        } else {
                                            v_arg_5100_ =
                                                leanh::lean_ctor_get(v___x_5089_, 1);
                                            leanh::lean_inc_ref(v_arg_5100_);
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
                                                                    leanh::lean_dec_ref(
                                                                        v___x_5101_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_5100_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_5088_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_5085_,
                                                                    );
                                                                    leanh::lean_dec_ref(
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
                                                                            leanh::lean_dec_ref(v_arg_5100_);
                                                                            v___x_5118_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17;
                                                                            v___x_5119_ = l_Lean_Expr_isConstOf(v___x_5113_, v___x_5118_);
                                                                            if v___x_5119_ == 0 {
                                                                                v___x_5120_ = l_Lean_Expr_isApp(v___x_5113_);
                                                                                if v___x_5120_ == 0
                                                                                {
                                                                                    leanh::lean_dec_ref(v___x_5113_);
                                                                                    leanh::lean_dec_ref(v_arg_5088_);
                                                                                    leanh::lean_dec_ref(v_arg_5085_);
                                                                                    leanh::lean_dec_ref(v_origExpr_5057_);
                                                                                    state = 4;
                                                                                    continue;
                                                                                } else {
                                                                                    v_arg_5121_ = leanh::lean_ctor_get(v___x_5113_, 1);
                                                                                    leanh::lean_inc_ref(v_arg_5121_);
                                                                                    v___x_5122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5113_);
                                                                                    v___x_5123_ = l_Lean_Expr_isApp(v___x_5122_);
                                                                                    if v___x_5123_
                                                                                        == 0
                                                                                    {
                                                                                        leanh::lean_dec_ref(v___x_5122_);
                                                                                        leanh::lean_dec_ref(v_arg_5121_);
                                                                                        leanh::lean_dec_ref(v_arg_5088_);
                                                                                        leanh::lean_dec_ref(v_arg_5085_);
                                                                                        leanh::lean_dec_ref(v_origExpr_5057_);
                                                                                        state = 4;
                                                                                        continue;
                                                                                    } else {
                                                                                        v_arg_5124_ = leanh::lean_ctor_get(v___x_5122_, 1);
                                                                                        leanh::lean_inc_ref(v_arg_5124_);
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
leanh::lean_dec_ref(v_arg_5124_);
leanh::lean_dec_ref(v_arg_5121_);
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
leanh::lean_dec_ref(v___x_5125_);
if v___x_5143_ == 0 {
leanh::lean_dec_ref(v_arg_5088_);
leanh::lean_dec_ref(v_arg_5085_);
leanh::lean_dec_ref(v_origExpr_5057_);
state = 4; continue;
} else {
leanh::lean_del_object(v___x_5076_);
v___x_5144_ = 0;
v___x_5145_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46;
v___x_5146_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5144_, v___x_5145_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5146_;
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_del_object(v___x_5076_);
v___x_5147_ = 2;
v___x_5148_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48;
v___x_5149_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5147_, v___x_5148_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5149_;
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_del_object(v___x_5076_);
v___x_5150_ = 3;
v___x_5151_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50;
v___x_5152_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5150_, v___x_5151_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5152_;
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_del_object(v___x_5076_);
v___x_5153_ = 4;
v___x_5154_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52;
v___x_5155_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5153_, v___x_5154_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5155_;
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_del_object(v___x_5076_);
v___x_5156_ = 5;
v___x_5157_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54;
v___x_5158_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5156_, v___x_5157_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5158_;
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_del_object(v___x_5076_);
v___x_5159_ = 6;
v___x_5160_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56;
v___x_5161_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_5088_, v_arg_5085_, v___x_5159_, v___x_5160_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
return v___x_5161_;
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_del_object(v___x_5076_);
leanh::lean_inc_ref(v_arg_5085_);
leanh::lean_inc_ref(v_arg_5121_);
v___x_5162_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_5121_, v_arg_5085_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if leanh::lean_obj_tag(v___x_5162_) == 0 {
v_a_5163_ = leanh::lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5216_ = (!leanh::lean_is_exclusive(v___x_5162_)) as u8;
if v_isSharedCheck_5216_ == 0 {
v___x_5165_ = v___x_5162_;
v_isShared_5166_ = v_isSharedCheck_5216_;
state = 6; continue;
} else {
leanh::lean_inc(v_a_5163_);
leanh::lean_dec(v___x_5162_);
v___x_5165_ = leanh::lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5216_;
state = 6; continue;
}
} else {
leanh::lean_dec_ref(v_arg_5124_);
leanh::lean_dec_ref(v_arg_5121_);
leanh::lean_dec_ref(v_arg_5088_);
leanh::lean_dec_ref(v_arg_5085_);
leanh::lean_dec_ref(v_origExpr_5057_);
v_a_5217_ = leanh::lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5224_ = (!leanh::lean_is_exclusive(v___x_5162_)) as u8;
if v_isSharedCheck_5224_ == 0 {
v___x_5219_ = v___x_5162_;
v_isShared_5220_ = v_isSharedCheck_5224_;
state = 16; continue;
} else {
leanh::lean_inc(v_a_5217_);
leanh::lean_dec(v___x_5162_);
v___x_5219_ = leanh::lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
state = 16; continue;
}
}
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_del_object(v___x_5076_);
leanh::lean_inc_ref(v_arg_5085_);
leanh::lean_inc_ref(v_arg_5121_);
v___x_5225_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_5121_, v_arg_5085_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if leanh::lean_obj_tag(v___x_5225_) == 0 {
v_a_5226_ = leanh::lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5279_ = (!leanh::lean_is_exclusive(v___x_5225_)) as u8;
if v_isSharedCheck_5279_ == 0 {
v___x_5228_ = v___x_5225_;
v_isShared_5229_ = v_isSharedCheck_5279_;
state = 18; continue;
} else {
leanh::lean_inc(v_a_5226_);
leanh::lean_dec(v___x_5225_);
v___x_5228_ = leanh::lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5279_;
state = 18; continue;
}
} else {
leanh::lean_dec_ref(v_arg_5124_);
leanh::lean_dec_ref(v_arg_5121_);
leanh::lean_dec_ref(v_arg_5088_);
leanh::lean_dec_ref(v_arg_5085_);
leanh::lean_dec_ref(v_origExpr_5057_);
v_a_5280_ = leanh::lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5287_ = (!leanh::lean_is_exclusive(v___x_5225_)) as u8;
if v_isSharedCheck_5287_ == 0 {
v___x_5282_ = v___x_5225_;
v_isShared_5283_ = v_isSharedCheck_5287_;
state = 28; continue;
} else {
leanh::lean_inc(v_a_5280_);
leanh::lean_dec(v___x_5225_);
v___x_5282_ = leanh::lean_box(0);
v_isShared_5283_ = v_isSharedCheck_5287_;
state = 28; continue;
}
}
}
} else {
leanh::lean_dec_ref(v___x_5125_);
leanh::lean_dec_ref(v_arg_5124_);
leanh::lean_dec_ref(v_arg_5121_);
leanh::lean_del_object(v___x_5076_);
leanh::lean_inc_ref(v_arg_5088_);
v___x_5288_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5088_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
if leanh::lean_obj_tag(v___x_5288_) == 0 {
v_a_5289_ = leanh::lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5352_ = (!leanh::lean_is_exclusive(v___x_5288_)) as u8;
if v_isSharedCheck_5352_ == 0 {
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5352_;
state = 30; continue;
} else {
leanh::lean_inc(v_a_5289_);
leanh::lean_dec(v___x_5288_);
v___x_5291_ = leanh::lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5352_;
state = 30; continue;
}
} else {
leanh::lean_dec_ref(v_arg_5088_);
leanh::lean_dec_ref(v_arg_5085_);
leanh::lean_dec_ref(v_origExpr_5057_);
return v___x_5288_;
}
}
                                                                                    }
                                                                                }
                                                                            } else {
                                                                                leanh::lean_dec_ref(v___x_5113_);
                                                                                leanh::lean_del_object(v___x_5076_);
                                                                                v___f_5353_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72;
                                                                                v___x_5354_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74;
                                                                                v___x_5355_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76;
                                                                                v___x_5356_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_5085_, v_arg_5088_, v___f_5353_, v___x_5354_, v___x_5355_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                                return v___x_5356_;
                                                                            }
                                                                        } else {
                                                                            leanh::lean_dec_ref(v___x_5113_);
                                                                            leanh::lean_del_object(v___x_5076_);
                                                                            v___x_5357_ = l_Lean_Meta_getNatValue_x3f(v_arg_5100_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                            if leanh::lean_obj_tag(v___x_5357_) == 0 {
v_a_5358_ = leanh::lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5420_ = (!leanh::lean_is_exclusive(v___x_5357_)) as u8;
if v_isSharedCheck_5420_ == 0 {
v___x_5360_ = v___x_5357_;
v_isShared_5361_ = v_isSharedCheck_5420_;
state = 40; continue;
} else {
leanh::lean_inc(v_a_5358_);
leanh::lean_dec(v___x_5357_);
v___x_5360_ = leanh::lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5420_;
state = 40; continue;
}
} else {
leanh::lean_dec_ref(v_arg_5100_);
leanh::lean_dec_ref(v_arg_5088_);
leanh::lean_dec_ref(v_arg_5085_);
leanh::lean_dec_ref(v_origExpr_5057_);
v_a_5421_ = leanh::lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5428_ = (!leanh::lean_is_exclusive(v___x_5357_)) as u8;
if v_isSharedCheck_5428_ == 0 {
v___x_5423_ = v___x_5357_;
v_isShared_5424_ = v_isSharedCheck_5428_;
state = 51; continue;
} else {
leanh::lean_inc(v_a_5421_);
leanh::lean_dec(v___x_5357_);
v___x_5423_ = leanh::lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
state = 51; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_5113_,
                                                                        );
                                                                        leanh::lean_del_object(v___x_5076_);
                                                                        leanh::lean_inc_ref(
                                                                            v_origExpr_5057_,
                                                                        );
                                                                        v___x_5429_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_origExpr_5057_, v___x_5115_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                        if leanh::lean_obj_tag(v___x_5429_) == 0 {
v_a_5430_ = leanh::lean_ctor_get(v___x_5429_, 0);
v_isSharedCheck_5497_ = (!leanh::lean_is_exclusive(v___x_5429_)) as u8;
if v_isSharedCheck_5497_ == 0 {
v___x_5432_ = v___x_5429_;
v_isShared_5433_ = v_isSharedCheck_5497_;
state = 53; continue;
} else {
leanh::lean_inc(v_a_5430_);
leanh::lean_dec(v___x_5429_);
v___x_5432_ = leanh::lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5497_;
state = 53; continue;
}
} else {
leanh::lean_dec_ref(v_arg_5100_);
leanh::lean_dec_ref(v_arg_5088_);
leanh::lean_dec_ref(v_arg_5085_);
leanh::lean_dec_ref(v_origExpr_5057_);
return v___x_5429_;
}
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_5101_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_5100_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_5088_,
                                                                );
                                                                leanh::lean_del_object(
                                                                    v___x_5076_,
                                                                );
                                                                v___x_5498_ =
                                                                    leanh::lean_box(0);
                                                                v___x_5499_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81;
                                                                v___x_5500_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5498_, v___x_5499_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                                return v___x_5500_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v___x_5101_);
                                                            leanh::lean_dec_ref(v_arg_5100_);
                                                            leanh::lean_del_object(
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
                                                            leanh::lean_dec_ref(v_arg_5085_);
                                                            if leanh::lean_obj_tag(
                                                                v___x_5501_,
                                                            ) == 0
                                                            {
                                                                v_a_5502_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5501_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5515_ = (!leanh::lean_is_exclusive(v___x_5501_)) as u8;
                                                                if v_isSharedCheck_5515_ == 0 {
                                                                    v___x_5504_ = v___x_5501_;
                                                                    v_isShared_5505_ =
                                                                        v_isSharedCheck_5515_;
                                                                    state = 67;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_5502_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_5501_,
                                                                    );
                                                                    v___x_5504_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_5505_ =
                                                                        v_isSharedCheck_5515_;
                                                                    state = 67;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v_arg_5088_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_origExpr_5057_,
                                                                );
                                                                v_a_5516_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_5501_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_5523_ = (!leanh::lean_is_exclusive(v___x_5501_)) as u8;
                                                                if v_isSharedCheck_5523_ == 0 {
                                                                    v___x_5518_ = v___x_5501_;
                                                                    v_isShared_5519_ =
                                                                        v_isSharedCheck_5523_;
                                                                    state = 69;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_5516_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_5501_,
                                                                    );
                                                                    v___x_5518_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_5519_ =
                                                                        v_isSharedCheck_5523_;
                                                                    state = 69;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref(v___x_5101_);
                                                        leanh::lean_dec_ref(v_arg_5100_);
                                                        leanh::lean_del_object(v___x_5076_);
                                                        leanh::lean_inc_ref(v_arg_5085_);
                                                        v___x_5524_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                        if leanh::lean_obj_tag(v___x_5524_)
                                                            == 0
                                                        {
                                                            v_a_5525_ = leanh::lean_ctor_get(
                                                                v___x_5524_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5593_ =
                                                                (!leanh::lean_is_exclusive(
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
                                                                leanh::lean_inc(v_a_5525_);
                                                                leanh::lean_dec(v___x_5524_);
                                                                v___x_5527_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_5528_ =
                                                                    v_isSharedCheck_5593_;
                                                                state = 71;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v_arg_5088_);
                                                            leanh::lean_dec_ref(v_arg_5085_);
                                                            leanh::lean_dec_ref(
                                                                v_origExpr_5057_,
                                                            );
                                                            return v___x_5524_;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_5101_);
                                                    leanh::lean_dec_ref(v_arg_5100_);
                                                    leanh::lean_del_object(v___x_5076_);
                                                    v___f_5594_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87;
                                                    v___x_5595_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5;
                                                    v___x_5596_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89;
                                                    v___x_5597_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_5085_, v_arg_5088_, v___f_5594_, v___x_5595_, v___x_5596_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                    leanh::lean_dec_ref(v_arg_5085_);
                                                    return v___x_5597_;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_5101_);
                                                leanh::lean_dec_ref(v_arg_5100_);
                                                leanh::lean_del_object(v___x_5076_);
                                                v___f_5598_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90;
                                                v___x_5599_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8;
                                                v___x_5600_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92;
                                                v___x_5601_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_5085_, v_arg_5088_, v___f_5598_, v___x_5599_, v___x_5600_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                                leanh::lean_dec_ref(v_arg_5085_);
                                                return v___x_5601_;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_5089_);
                                        leanh::lean_dec_ref(v_arg_5088_);
                                        leanh::lean_dec_ref(v_arg_5085_);
                                        leanh::lean_del_object(v___x_5076_);
                                        v___x_5602_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_origExpr_5057_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                        return v___x_5602_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_5089_);
                                    leanh::lean_dec_ref(v_arg_5088_);
                                    leanh::lean_del_object(v___x_5076_);
                                    v___x_5603_ = leanh::lean_box(4);
                                    v___x_5604_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94;
                                    v___x_5605_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5603_, v___x_5604_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                    return v___x_5605_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_5089_);
                                leanh::lean_dec_ref(v_arg_5088_);
                                leanh::lean_del_object(v___x_5076_);
                                v___x_5606_ = leanh::lean_box(5);
                                v___x_5607_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96;
                                v___x_5608_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5606_, v___x_5607_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                                return v___x_5608_;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_5089_);
                            leanh::lean_dec_ref(v_arg_5088_);
                            leanh::lean_del_object(v___x_5076_);
                            v___x_5609_ = leanh::lean_box(6);
                            v___x_5610_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98;
                            v___x_5611_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_5085_, v___x_5609_, v___x_5610_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                            return v___x_5611_;
                        }
                    }
                }
            }
            4 => {
                v___x_5079_ = leanh::lean_box(0);
                if v_isShared_5077_ == 0 {
                    leanh::lean_ctor_set(v___x_5076_, 0, v___x_5079_);
                    v___x_5081_ = v___x_5076_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5082_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5079_);
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
                    leanh::lean_dec_ref(v___x_5172_);
                    leanh::lean_dec(v_a_5163_);
                    leanh::lean_dec_ref(v_arg_5121_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 7;
                    continue;
                } else {
                    v_arg_5174_ = leanh::lean_ctor_get(v___x_5172_, 1);
                    leanh::lean_inc_ref(v_arg_5174_);
                    v___x_5175_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5172_);
                    v___x_5176_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                    v___x_5177_ = l_Lean_Expr_isConstOf(v___x_5175_, v___x_5176_);
                    leanh::lean_dec_ref(v___x_5175_);
                    if v___x_5177_ == 0 {
                        leanh::lean_dec_ref(v_arg_5174_);
                        leanh::lean_dec(v_a_5163_);
                        leanh::lean_dec_ref(v_arg_5121_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_5165_);
                        v___x_5178_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_5174_,
                            v_a_5060_,
                            v_a_5061_,
                            v_a_5062_,
                            v_a_5063_,
                        );
                        leanh::lean_dec_ref(v_arg_5174_);
                        if leanh::lean_obj_tag(v___x_5178_) == 0 {
                            v_a_5179_ = leanh::lean_ctor_get(v___x_5178_, 0);
                            leanh::lean_inc(v_a_5179_);
                            leanh::lean_dec_ref_known(v___x_5178_, 1);
                            v___f_5180_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57;
                            if leanh::lean_obj_tag(v_a_5179_) == 0 {
                                v___y_5207_ = v___x_5129_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_a_5179_, 1);
                                v___y_5207_ = v___x_5177_;
                                state = 13;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5163_);
                            leanh::lean_dec_ref(v_arg_5121_);
                            leanh::lean_dec_ref(v_arg_5088_);
                            leanh::lean_dec_ref(v_arg_5085_);
                            leanh::lean_dec_ref(v_origExpr_5057_);
                            v_a_5208_ = leanh::lean_ctor_get(v___x_5178_, 0);
                            v_isSharedCheck_5215_ =
                                (!leanh::lean_is_exclusive(v___x_5178_)) as u8;
                            if v_isSharedCheck_5215_ == 0 {
                                v___x_5210_ = v___x_5178_;
                                v_isShared_5211_ = v_isSharedCheck_5215_;
                                state = 14;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5208_);
                                leanh::lean_dec(v___x_5178_);
                                v___x_5210_ = leanh::lean_box(0);
                                v_isShared_5211_ = v_isSharedCheck_5215_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                v___x_5168_ = leanh::lean_box(0);
                if v_isShared_5166_ == 0 {
                    leanh::lean_ctor_set(v___x_5165_, 0, v___x_5168_);
                    v___x_5170_ = v___x_5165_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5168_);
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
                    leanh::lean_dec_ref(v___x_5188_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 1;
                    continue;
                } else {
                    v___x_5190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5188_);
                    v___x_5191_ = l_Lean_Expr_isConstOf(v___x_5190_, v___x_5176_);
                    leanh::lean_dec_ref(v___x_5190_);
                    if v___x_5191_ == 0 {
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
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
                v___x_5196_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63);
                v___x_5197_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v___x_5196_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if leanh::lean_obj_tag(v___x_5197_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5197_, 1);
                    v___y_5182_ = v_a_5058_;
                    v___y_5183_ = v_a_5059_;
                    v___y_5184_ = v_a_5060_;
                    v___y_5185_ = v_a_5061_;
                    v___y_5186_ = v_a_5062_;
                    v___y_5187_ = v_a_5063_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_arg_5121_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5198_ = leanh::lean_ctor_get(v___x_5197_, 0);
                    v_isSharedCheck_5205_ = (!leanh::lean_is_exclusive(v___x_5197_)) as u8;
                    if v_isSharedCheck_5205_ == 0 {
                        v___x_5200_ = v___x_5197_;
                        v_isShared_5201_ = v_isSharedCheck_5205_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5198_);
                        leanh::lean_dec(v___x_5197_);
                        v___x_5200_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_a_5198_);
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
                    leanh::lean_dec(v_a_5163_);
                    v___y_5182_ = v_a_5058_;
                    v___y_5183_ = v_a_5059_;
                    v___y_5184_ = v_a_5060_;
                    v___y_5185_ = v_a_5061_;
                    v___y_5186_ = v_a_5062_;
                    v___y_5187_ = v_a_5063_;
                    state = 9;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v_a_5163_) == 0 {
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
                        leanh::lean_dec_ref_known(v_a_5163_, 1);
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
                    v_reuseFailAlloc_5214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5214_, 0, v_a_5208_);
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
                    v_reuseFailAlloc_5223_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
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
                    leanh::lean_dec_ref(v___x_5235_);
                    leanh::lean_dec(v_a_5226_);
                    leanh::lean_dec_ref(v_arg_5121_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 19;
                    continue;
                } else {
                    v_arg_5237_ = leanh::lean_ctor_get(v___x_5235_, 1);
                    leanh::lean_inc_ref(v_arg_5237_);
                    v___x_5238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5235_);
                    v___x_5239_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8;
                    v___x_5240_ = l_Lean_Expr_isConstOf(v___x_5238_, v___x_5239_);
                    leanh::lean_dec_ref(v___x_5238_);
                    if v___x_5240_ == 0 {
                        leanh::lean_dec_ref(v_arg_5237_);
                        leanh::lean_dec(v_a_5226_);
                        leanh::lean_dec_ref(v_arg_5121_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_5228_);
                        v___x_5241_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_5237_,
                            v_a_5060_,
                            v_a_5061_,
                            v_a_5062_,
                            v_a_5063_,
                        );
                        leanh::lean_dec_ref(v_arg_5237_);
                        if leanh::lean_obj_tag(v___x_5241_) == 0 {
                            v_a_5242_ = leanh::lean_ctor_get(v___x_5241_, 0);
                            leanh::lean_inc(v_a_5242_);
                            leanh::lean_dec_ref_known(v___x_5241_, 1);
                            v___f_5243_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64;
                            if leanh::lean_obj_tag(v_a_5242_) == 0 {
                                v___y_5270_ = v___x_5127_;
                                state = 25;
                                continue;
                            } else {
                                leanh::lean_dec_ref_known(v_a_5242_, 1);
                                v___y_5270_ = v___x_5240_;
                                state = 25;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5226_);
                            leanh::lean_dec_ref(v_arg_5121_);
                            leanh::lean_dec_ref(v_arg_5088_);
                            leanh::lean_dec_ref(v_arg_5085_);
                            leanh::lean_dec_ref(v_origExpr_5057_);
                            v_a_5271_ = leanh::lean_ctor_get(v___x_5241_, 0);
                            v_isSharedCheck_5278_ =
                                (!leanh::lean_is_exclusive(v___x_5241_)) as u8;
                            if v_isSharedCheck_5278_ == 0 {
                                v___x_5273_ = v___x_5241_;
                                v_isShared_5274_ = v_isSharedCheck_5278_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5271_);
                                leanh::lean_dec(v___x_5241_);
                                v___x_5273_ = leanh::lean_box(0);
                                v_isShared_5274_ = v_isSharedCheck_5278_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                }
            }
            19 => {
                v___x_5231_ = leanh::lean_box(0);
                if v_isShared_5229_ == 0 {
                    leanh::lean_ctor_set(v___x_5228_, 0, v___x_5231_);
                    v___x_5233_ = v___x_5228_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5234_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
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
                    leanh::lean_dec_ref(v___x_5251_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    state = 2;
                    continue;
                } else {
                    v___x_5253_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5251_);
                    v___x_5254_ = l_Lean_Expr_isConstOf(v___x_5253_, v___x_5239_);
                    leanh::lean_dec_ref(v___x_5253_);
                    if v___x_5254_ == 0 {
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
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
                v___x_5259_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63);
                v___x_5260_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v___x_5259_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if leanh::lean_obj_tag(v___x_5260_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5260_, 1);
                    v___y_5245_ = v_a_5058_;
                    v___y_5246_ = v_a_5059_;
                    v___y_5247_ = v_a_5060_;
                    v___y_5248_ = v_a_5061_;
                    v___y_5249_ = v_a_5062_;
                    v___y_5250_ = v_a_5063_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_arg_5121_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5261_ = leanh::lean_ctor_get(v___x_5260_, 0);
                    v_isSharedCheck_5268_ = (!leanh::lean_is_exclusive(v___x_5260_)) as u8;
                    if v_isSharedCheck_5268_ == 0 {
                        v___x_5263_ = v___x_5260_;
                        v_isShared_5264_ = v_isSharedCheck_5268_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5261_);
                        leanh::lean_dec(v___x_5260_);
                        v___x_5263_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5267_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5267_, 0, v_a_5261_);
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
                    leanh::lean_dec(v_a_5226_);
                    v___y_5245_ = v_a_5058_;
                    v___y_5246_ = v_a_5059_;
                    v___y_5247_ = v_a_5060_;
                    v___y_5248_ = v_a_5061_;
                    v___y_5249_ = v_a_5062_;
                    v___y_5250_ = v_a_5063_;
                    state = 21;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v_a_5226_) == 0 {
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
                        leanh::lean_dec_ref_known(v_a_5226_, 1);
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
                    v_reuseFailAlloc_5277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5277_, 0, v_a_5271_);
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
                    v_reuseFailAlloc_5286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5280_);
                    v___x_5285_ = v_reuseFailAlloc_5286_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5285_;
            }
            30 => {
                if leanh::lean_obj_tag(v_a_5289_) == 1 {
                    leanh::lean_del_object(v___x_5291_);
                    v_val_5293_ = leanh::lean_ctor_get(v_a_5289_, 0);
                    leanh::lean_inc(v_val_5293_);
                    leanh::lean_dec_ref_known(v_a_5289_, 1);
                    leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5294_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if leanh::lean_obj_tag(v___x_5294_) == 0 {
                        v_a_5295_ = leanh::lean_ctor_get(v___x_5294_, 0);
                        v_isSharedCheck_5347_ =
                            (!leanh::lean_is_exclusive(v___x_5294_)) as u8;
                        if v_isSharedCheck_5347_ == 0 {
                            v___x_5297_ = v___x_5294_;
                            v_isShared_5298_ = v_isSharedCheck_5347_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5295_);
                            leanh::lean_dec(v___x_5294_);
                            v___x_5297_ = leanh::lean_box(0);
                            v_isShared_5298_ = v_isSharedCheck_5347_;
                            state = 31;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5293_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5294_;
                    }
                } else {
                    leanh::lean_dec(v_a_5289_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5348_ = leanh::lean_box(0);
                    if v_isShared_5292_ == 0 {
                        leanh::lean_ctor_set(v___x_5291_, 0, v___x_5348_);
                        v___x_5350_ = v___x_5291_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_5351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5348_);
                        v___x_5350_ = v_reuseFailAlloc_5351_;
                        state = 39;
                        continue;
                    }
                }
            }
            31 => {
                if leanh::lean_obj_tag(v_a_5295_) == 1 {
                    leanh::lean_del_object(v___x_5297_);
                    v_val_5299_ = leanh::lean_ctor_get(v_a_5295_, 0);
                    v_isSharedCheck_5342_ = (!leanh::lean_is_exclusive(v_a_5295_)) as u8;
                    if v_isSharedCheck_5342_ == 0 {
                        v___x_5301_ = v_a_5295_;
                        v_isShared_5302_ = v_isSharedCheck_5342_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5299_);
                        leanh::lean_dec(v_a_5295_);
                        v___x_5301_ = leanh::lean_box(0);
                        v_isShared_5302_ = v_isSharedCheck_5342_;
                        state = 32;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5295_);
                    leanh::lean_dec(v_val_5293_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5343_ = leanh::lean_box(0);
                    if v_isShared_5298_ == 0 {
                        leanh::lean_ctor_set(v___x_5297_, 0, v___x_5343_);
                        v___x_5345_ = v___x_5297_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_5346_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5343_);
                        v___x_5345_ = v_reuseFailAlloc_5346_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v_width_5303_ = leanh::lean_ctor_get(v_val_5293_, 0);
                leanh::lean_inc_n(v_width_5303_, 2);
                v_bvExpr_5304_ = leanh::lean_ctor_get(v_val_5293_, 1);
                v_expr_5305_ = leanh::lean_ctor_get(v_val_5293_, 4);
                leanh::lean_inc_ref(v_expr_5305_);
                v_width_5306_ = leanh::lean_ctor_get(v_val_5299_, 0);
                leanh::lean_inc_n(v_width_5306_, 2);
                v_bvExpr_5307_ = leanh::lean_ctor_get(v_val_5299_, 1);
                v_expr_5308_ = leanh::lean_ctor_get(v_val_5299_, 4);
                leanh::lean_inc_ref(v_expr_5308_);
                v___x_5309_ = lean_nat_add(v_width_5303_, v_width_5306_);
                leanh::lean_inc_ref(v_bvExpr_5307_);
                leanh::lean_inc_ref(v_bvExpr_5304_);
                leanh::lean_inc_n(v___x_5309_, 2);
                v___x_5310_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(
                    v_width_5303_,
                    v_width_5306_,
                    v___x_5309_,
                    v_bvExpr_5304_,
                    v_bvExpr_5307_,
                );
                v___x_5311_ = l_Lean_mkNatLit(v___x_5309_);
                leanh::lean_inc_ref(v___x_5311_);
                v___x_5312_ =
                    l_Lean_Meta_mkEqRefl(v___x_5311_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if leanh::lean_obj_tag(v___x_5312_) == 0 {
                    v_a_5313_ = leanh::lean_ctor_get(v___x_5312_, 0);
                    v_isSharedCheck_5333_ = (!leanh::lean_is_exclusive(v___x_5312_)) as u8;
                    if v_isSharedCheck_5333_ == 0 {
                        v___x_5315_ = v___x_5312_;
                        v_isShared_5316_ = v_isSharedCheck_5333_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5313_);
                        leanh::lean_dec(v___x_5312_);
                        v___x_5315_ = leanh::lean_box(0);
                        v_isShared_5316_ = v_isSharedCheck_5333_;
                        state = 33;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5311_);
                    leanh::lean_dec_ref(v___x_5310_);
                    leanh::lean_dec(v___x_5309_);
                    leanh::lean_dec_ref(v_expr_5308_);
                    leanh::lean_dec(v_width_5306_);
                    leanh::lean_dec_ref(v_expr_5305_);
                    leanh::lean_dec(v_width_5303_);
                    leanh::lean_del_object(v___x_5301_);
                    leanh::lean_dec(v_val_5299_);
                    leanh::lean_dec(v_val_5293_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5334_ = leanh::lean_ctor_get(v___x_5312_, 0);
                    v_isSharedCheck_5341_ = (!leanh::lean_is_exclusive(v___x_5312_)) as u8;
                    if v_isSharedCheck_5341_ == 0 {
                        v___x_5336_ = v___x_5312_;
                        v_isShared_5337_ = v_isSharedCheck_5341_;
                        state = 36;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5334_);
                        leanh::lean_dec(v___x_5312_);
                        v___x_5336_ = leanh::lean_box(0);
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
                v___x_5320_ = leanh::lean_box(0);
                v___x_5321_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71);
                leanh::lean_inc(v_width_5303_);
                v___x_5322_ = l_Lean_mkNatLit(v_width_5303_);
                leanh::lean_inc(v_width_5306_);
                v___x_5323_ = l_Lean_mkNatLit(v_width_5306_);
                leanh::lean_inc_ref(v___x_5323_);
                leanh::lean_inc_ref(v___x_5322_);
                leanh::lean_inc_ref(v_expr_5308_);
                leanh::lean_inc_ref(v_expr_5305_);
                v___f_5324_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0___boxed as *mut core::ffi::c_void, 21, 15);
                leanh::lean_closure_set(v___f_5324_, 0, v_width_5303_);
                leanh::lean_closure_set(v___f_5324_, 1, v_expr_5305_);
                leanh::lean_closure_set(v___f_5324_, 2, v_width_5306_);
                leanh::lean_closure_set(v___f_5324_, 3, v_expr_5308_);
                leanh::lean_closure_set(v___f_5324_, 4, v_val_5293_);
                leanh::lean_closure_set(v___f_5324_, 5, v_val_5299_);
                leanh::lean_closure_set(v___f_5324_, 6, v___x_5317_);
                leanh::lean_closure_set(v___f_5324_, 7, v___x_5318_);
                leanh::lean_closure_set(v___f_5324_, 8, v___x_5319_);
                leanh::lean_closure_set(v___f_5324_, 9, v___x_5090_);
                leanh::lean_closure_set(v___f_5324_, 10, v___x_5320_);
                leanh::lean_closure_set(v___f_5324_, 11, v___x_5322_);
                leanh::lean_closure_set(v___f_5324_, 12, v___x_5323_);
                leanh::lean_closure_set(v___f_5324_, 13, v_arg_5088_);
                leanh::lean_closure_set(v___f_5324_, 14, v_arg_5085_);
                v___x_5325_ = l_Lean_mkApp6(
                    v___x_5321_,
                    v___x_5322_,
                    v___x_5323_,
                    v___x_5311_,
                    v_expr_5305_,
                    v_expr_5308_,
                    v_a_5313_,
                );
                v___x_5326_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5326_, 0, v___x_5309_);
                leanh::lean_ctor_set(v___x_5326_, 1, v___x_5310_);
                leanh::lean_ctor_set(v___x_5326_, 2, v_origExpr_5057_);
                leanh::lean_ctor_set(v___x_5326_, 3, v___f_5324_);
                leanh::lean_ctor_set(v___x_5326_, 4, v___x_5325_);
                if v_isShared_5302_ == 0 {
                    leanh::lean_ctor_set(v___x_5301_, 0, v___x_5326_);
                    v___x_5328_ = v___x_5301_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5332_, 0, v___x_5326_);
                    v___x_5328_ = v_reuseFailAlloc_5332_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_5316_ == 0 {
                    leanh::lean_ctor_set(v___x_5315_, 0, v___x_5328_);
                    v___x_5330_ = v___x_5315_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5331_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5328_);
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
                    v_reuseFailAlloc_5340_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
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
                if leanh::lean_obj_tag(v_a_5358_) == 1 {
                    leanh::lean_del_object(v___x_5360_);
                    v_val_5362_ = leanh::lean_ctor_get(v_a_5358_, 0);
                    leanh::lean_inc(v_val_5362_);
                    leanh::lean_dec_ref_known(v_a_5358_, 1);
                    v___x_5363_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_5088_,
                        v_a_5060_,
                        v_a_5061_,
                        v_a_5062_,
                        v_a_5063_,
                    );
                    if leanh::lean_obj_tag(v___x_5363_) == 0 {
                        v_a_5364_ = leanh::lean_ctor_get(v___x_5363_, 0);
                        v_isSharedCheck_5407_ =
                            (!leanh::lean_is_exclusive(v___x_5363_)) as u8;
                        if v_isSharedCheck_5407_ == 0 {
                            v___x_5366_ = v___x_5363_;
                            v_isShared_5367_ = v_isSharedCheck_5407_;
                            state = 41;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5364_);
                            leanh::lean_dec(v___x_5363_);
                            v___x_5366_ = leanh::lean_box(0);
                            v_isShared_5367_ = v_isSharedCheck_5407_;
                            state = 41;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5362_);
                        leanh::lean_dec_ref(v_arg_5100_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5408_ = leanh::lean_ctor_get(v___x_5363_, 0);
                        v_isSharedCheck_5415_ =
                            (!leanh::lean_is_exclusive(v___x_5363_)) as u8;
                        if v_isSharedCheck_5415_ == 0 {
                            v___x_5410_ = v___x_5363_;
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 48;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5408_);
                            leanh::lean_dec(v___x_5363_);
                            v___x_5410_ = leanh::lean_box(0);
                            v_isShared_5411_ = v_isSharedCheck_5415_;
                            state = 48;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5358_);
                    leanh::lean_dec_ref(v_arg_5100_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5416_ = leanh::lean_box(0);
                    if v_isShared_5361_ == 0 {
                        leanh::lean_ctor_set(v___x_5360_, 0, v___x_5416_);
                        v___x_5418_ = v___x_5360_;
                        state = 50;
                        continue;
                    } else {
                        v_reuseFailAlloc_5419_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5416_);
                        v___x_5418_ = v_reuseFailAlloc_5419_;
                        state = 50;
                        continue;
                    }
                }
            }
            41 => {
                if leanh::lean_obj_tag(v_a_5364_) == 1 {
                    leanh::lean_del_object(v___x_5366_);
                    v_val_5368_ = leanh::lean_ctor_get(v_a_5364_, 0);
                    leanh::lean_inc(v_val_5368_);
                    leanh::lean_dec_ref_known(v_a_5364_, 1);
                    leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5369_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if leanh::lean_obj_tag(v___x_5369_) == 0 {
                        v_a_5370_ = leanh::lean_ctor_get(v___x_5369_, 0);
                        v_isSharedCheck_5402_ =
                            (!leanh::lean_is_exclusive(v___x_5369_)) as u8;
                        if v_isSharedCheck_5402_ == 0 {
                            v___x_5372_ = v___x_5369_;
                            v_isShared_5373_ = v_isSharedCheck_5402_;
                            state = 42;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5370_);
                            leanh::lean_dec(v___x_5369_);
                            v___x_5372_ = leanh::lean_box(0);
                            v_isShared_5373_ = v_isSharedCheck_5402_;
                            state = 42;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5368_);
                        leanh::lean_dec(v_val_5362_);
                        leanh::lean_dec_ref(v_arg_5100_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5369_;
                    }
                } else {
                    leanh::lean_dec(v_a_5364_);
                    leanh::lean_dec(v_val_5362_);
                    leanh::lean_dec_ref(v_arg_5100_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5403_ = leanh::lean_box(0);
                    if v_isShared_5367_ == 0 {
                        leanh::lean_ctor_set(v___x_5366_, 0, v___x_5403_);
                        v___x_5405_ = v___x_5366_;
                        state = 47;
                        continue;
                    } else {
                        v_reuseFailAlloc_5406_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5403_);
                        v___x_5405_ = v_reuseFailAlloc_5406_;
                        state = 47;
                        continue;
                    }
                }
            }
            42 => {
                if leanh::lean_obj_tag(v_a_5370_) == 1 {
                    v_val_5374_ = leanh::lean_ctor_get(v_a_5370_, 0);
                    v_isSharedCheck_5397_ = (!leanh::lean_is_exclusive(v_a_5370_)) as u8;
                    if v_isSharedCheck_5397_ == 0 {
                        v___x_5376_ = v_a_5370_;
                        v_isShared_5377_ = v_isSharedCheck_5397_;
                        state = 43;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5374_);
                        leanh::lean_dec(v_a_5370_);
                        v___x_5376_ = leanh::lean_box(0);
                        v_isShared_5377_ = v_isSharedCheck_5397_;
                        state = 43;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5370_);
                    leanh::lean_dec(v_val_5368_);
                    leanh::lean_dec(v_val_5362_);
                    leanh::lean_dec_ref(v_arg_5100_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5398_ = leanh::lean_box(0);
                    if v_isShared_5373_ == 0 {
                        leanh::lean_ctor_set(v___x_5372_, 0, v___x_5398_);
                        v___x_5400_ = v___x_5372_;
                        state = 46;
                        continue;
                    } else {
                        v_reuseFailAlloc_5401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5401_, 0, v___x_5398_);
                        v___x_5400_ = v_reuseFailAlloc_5401_;
                        state = 46;
                        continue;
                    }
                }
            }
            43 => {
                v_width_5378_ = leanh::lean_ctor_get(v_val_5374_, 0);
                leanh::lean_inc_n(v_width_5378_, 3);
                v_bvExpr_5379_ = leanh::lean_ctor_get(v_val_5374_, 1);
                v_expr_5380_ = leanh::lean_ctor_get(v_val_5374_, 4);
                leanh::lean_inc_ref_n(v_expr_5380_, 2);
                leanh::lean_inc_ref(v_bvExpr_5379_);
                leanh::lean_inc(v_val_5368_);
                v___x_5381_ = l_Std_Tactic_BVDecide_BVExpr_extract___override(
                    v_width_5378_,
                    v_val_5362_,
                    v_val_5368_,
                    v_bvExpr_5379_,
                );
                v___x_5382_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0;
                v___x_5383_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1;
                v___x_5384_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2;
                v___x_5385_ = leanh::lean_box(0);
                v___x_5386_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79);
                v___x_5387_ = l_Lean_mkNatLit(v_width_5378_);
                leanh::lean_inc_ref(v___x_5387_);
                leanh::lean_inc_ref(v_arg_5088_);
                leanh::lean_inc_ref(v_arg_5100_);
                v___f_5388_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1___boxed as *mut core::ffi::c_void, 18, 12);
                leanh::lean_closure_set(v___f_5388_, 0, v_width_5378_);
                leanh::lean_closure_set(v___f_5388_, 1, v_expr_5380_);
                leanh::lean_closure_set(v___f_5388_, 2, v_val_5374_);
                leanh::lean_closure_set(v___f_5388_, 3, v___x_5382_);
                leanh::lean_closure_set(v___f_5388_, 4, v___x_5383_);
                leanh::lean_closure_set(v___f_5388_, 5, v___x_5384_);
                leanh::lean_closure_set(v___f_5388_, 6, v___x_5090_);
                leanh::lean_closure_set(v___f_5388_, 7, v___x_5385_);
                leanh::lean_closure_set(v___f_5388_, 8, v_arg_5100_);
                leanh::lean_closure_set(v___f_5388_, 9, v_arg_5088_);
                leanh::lean_closure_set(v___f_5388_, 10, v___x_5387_);
                leanh::lean_closure_set(v___f_5388_, 11, v_arg_5085_);
                v___x_5389_ = l_Lean_mkApp4(
                    v___x_5386_,
                    v___x_5387_,
                    v_arg_5100_,
                    v_arg_5088_,
                    v_expr_5380_,
                );
                v___x_5390_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5390_, 0, v_val_5368_);
                leanh::lean_ctor_set(v___x_5390_, 1, v___x_5381_);
                leanh::lean_ctor_set(v___x_5390_, 2, v_origExpr_5057_);
                leanh::lean_ctor_set(v___x_5390_, 3, v___f_5388_);
                leanh::lean_ctor_set(v___x_5390_, 4, v___x_5389_);
                if v_isShared_5377_ == 0 {
                    leanh::lean_ctor_set(v___x_5376_, 0, v___x_5390_);
                    v___x_5392_ = v___x_5376_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5396_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5396_, 0, v___x_5390_);
                    v___x_5392_ = v_reuseFailAlloc_5396_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_5373_ == 0 {
                    leanh::lean_ctor_set(v___x_5372_, 0, v___x_5392_);
                    v___x_5394_ = v___x_5372_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_5395_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5395_, 0, v___x_5392_);
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
                    v_reuseFailAlloc_5414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
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
                    v_reuseFailAlloc_5427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
                    v___x_5426_ = v_reuseFailAlloc_5427_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5426_;
            }
            53 => {
                if leanh::lean_obj_tag(v_a_5430_) == 1 {
                    leanh::lean_del_object(v___x_5432_);
                    v_val_5434_ = leanh::lean_ctor_get(v_a_5430_, 0);
                    leanh::lean_inc_ref(v_arg_5100_);
                    v___x_5435_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(
                        v_arg_5100_,
                        v_a_5058_,
                        v_a_5059_,
                        v_a_5060_,
                        v_a_5061_,
                        v_a_5062_,
                        v_a_5063_,
                    );
                    if leanh::lean_obj_tag(v___x_5435_) == 0 {
                        v_a_5436_ = leanh::lean_ctor_get(v___x_5435_, 0);
                        v_isSharedCheck_5484_ =
                            (!leanh::lean_is_exclusive(v___x_5435_)) as u8;
                        if v_isSharedCheck_5484_ == 0 {
                            v___x_5438_ = v___x_5435_;
                            v_isShared_5439_ = v_isSharedCheck_5484_;
                            state = 54;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5436_);
                            leanh::lean_dec(v___x_5435_);
                            v___x_5438_ = leanh::lean_box(0);
                            v_isShared_5439_ = v_isSharedCheck_5484_;
                            state = 54;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_5430_, 1);
                        leanh::lean_dec_ref(v_arg_5100_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5485_ = leanh::lean_ctor_get(v___x_5435_, 0);
                        v_isSharedCheck_5492_ =
                            (!leanh::lean_is_exclusive(v___x_5435_)) as u8;
                        if v_isSharedCheck_5492_ == 0 {
                            v___x_5487_ = v___x_5435_;
                            v_isShared_5488_ = v_isSharedCheck_5492_;
                            state = 64;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5485_);
                            leanh::lean_dec(v___x_5435_);
                            v___x_5487_ = leanh::lean_box(0);
                            v_isShared_5488_ = v_isSharedCheck_5492_;
                            state = 64;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5430_);
                    leanh::lean_dec_ref(v_arg_5100_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5493_ = leanh::lean_box(0);
                    if v_isShared_5433_ == 0 {
                        leanh::lean_ctor_set(v___x_5432_, 0, v___x_5493_);
                        v___x_5495_ = v___x_5432_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_5496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
                        v___x_5495_ = v_reuseFailAlloc_5496_;
                        state = 66;
                        continue;
                    }
                }
            }
            54 => {
                if leanh::lean_obj_tag(v_a_5436_) == 1 {
                    leanh::lean_del_object(v___x_5438_);
                    v_val_5440_ = leanh::lean_ctor_get(v_a_5436_, 0);
                    leanh::lean_inc(v_val_5440_);
                    leanh::lean_dec_ref_known(v_a_5436_, 1);
                    leanh::lean_inc_ref(v_arg_5088_);
                    v___x_5441_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5088_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if leanh::lean_obj_tag(v___x_5441_) == 0 {
                        v_a_5442_ = leanh::lean_ctor_get(v___x_5441_, 0);
                        v_isSharedCheck_5479_ =
                            (!leanh::lean_is_exclusive(v___x_5441_)) as u8;
                        if v_isSharedCheck_5479_ == 0 {
                            v___x_5444_ = v___x_5441_;
                            v_isShared_5445_ = v_isSharedCheck_5479_;
                            state = 55;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5442_);
                            leanh::lean_dec(v___x_5441_);
                            v___x_5444_ = leanh::lean_box(0);
                            v_isShared_5445_ = v_isSharedCheck_5479_;
                            state = 55;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5440_);
                        leanh::lean_dec_ref_known(v_a_5430_, 1);
                        leanh::lean_dec_ref(v_arg_5100_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5441_;
                    }
                } else {
                    leanh::lean_dec(v_a_5436_);
                    leanh::lean_dec_ref_known(v_a_5430_, 1);
                    leanh::lean_dec_ref(v_arg_5100_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5480_ = leanh::lean_box(0);
                    if v_isShared_5439_ == 0 {
                        leanh::lean_ctor_set(v___x_5438_, 0, v___x_5480_);
                        v___x_5482_ = v___x_5438_;
                        state = 63;
                        continue;
                    } else {
                        v_reuseFailAlloc_5483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5480_);
                        v___x_5482_ = v_reuseFailAlloc_5483_;
                        state = 63;
                        continue;
                    }
                }
            }
            55 => {
                if leanh::lean_obj_tag(v_a_5442_) == 1 {
                    leanh::lean_del_object(v___x_5444_);
                    v_val_5446_ = leanh::lean_ctor_get(v_a_5442_, 0);
                    leanh::lean_inc(v_val_5446_);
                    leanh::lean_dec_ref_known(v_a_5442_, 1);
                    leanh::lean_inc_ref(v_arg_5085_);
                    v___x_5447_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_5085_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    if leanh::lean_obj_tag(v___x_5447_) == 0 {
                        v_a_5448_ = leanh::lean_ctor_get(v___x_5447_, 0);
                        v_isSharedCheck_5474_ =
                            (!leanh::lean_is_exclusive(v___x_5447_)) as u8;
                        if v_isSharedCheck_5474_ == 0 {
                            v___x_5450_ = v___x_5447_;
                            v_isShared_5451_ = v_isSharedCheck_5474_;
                            state = 56;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5448_);
                            leanh::lean_dec(v___x_5447_);
                            v___x_5450_ = leanh::lean_box(0);
                            v_isShared_5451_ = v_isSharedCheck_5474_;
                            state = 56;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5446_);
                        leanh::lean_dec(v_val_5440_);
                        leanh::lean_dec_ref_known(v_a_5430_, 1);
                        leanh::lean_dec_ref(v_arg_5100_);
                        leanh::lean_dec_ref(v_arg_5088_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        return v___x_5447_;
                    }
                } else {
                    leanh::lean_dec(v_a_5442_);
                    leanh::lean_dec(v_val_5440_);
                    leanh::lean_dec_ref_known(v_a_5430_, 1);
                    leanh::lean_dec_ref(v_arg_5100_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5475_ = leanh::lean_box(0);
                    if v_isShared_5445_ == 0 {
                        leanh::lean_ctor_set(v___x_5444_, 0, v___x_5475_);
                        v___x_5477_ = v___x_5444_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_5478_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5475_);
                        v___x_5477_ = v_reuseFailAlloc_5478_;
                        state = 62;
                        continue;
                    }
                }
            }
            56 => {
                if leanh::lean_obj_tag(v_a_5448_) == 1 {
                    leanh::lean_del_object(v___x_5450_);
                    v_val_5452_ = leanh::lean_ctor_get(v_a_5448_, 0);
                    leanh::lean_inc(v_val_5452_);
                    leanh::lean_dec_ref_known(v_a_5448_, 1);
                    leanh::lean_inc(v_val_5434_);
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
                    if leanh::lean_obj_tag(v___x_5453_) == 0 {
                        v_isSharedCheck_5460_ =
                            (!leanh::lean_is_exclusive(v___x_5453_)) as u8;
                        if v_isSharedCheck_5460_ == 0 {
                            v_unused_5461_ = leanh::lean_ctor_get(v___x_5453_, 0);
                            leanh::lean_dec(v_unused_5461_);
                            v___x_5455_ = v___x_5453_;
                            v_isShared_5456_ = v_isSharedCheck_5460_;
                            state = 57;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5453_);
                            v___x_5455_ = leanh::lean_box(0);
                            v_isShared_5456_ = v_isSharedCheck_5460_;
                            state = 57;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_5430_, 1);
                        v_a_5462_ = leanh::lean_ctor_get(v___x_5453_, 0);
                        v_isSharedCheck_5469_ =
                            (!leanh::lean_is_exclusive(v___x_5453_)) as u8;
                        if v_isSharedCheck_5469_ == 0 {
                            v___x_5464_ = v___x_5453_;
                            v_isShared_5465_ = v_isSharedCheck_5469_;
                            state = 59;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5462_);
                            leanh::lean_dec(v___x_5453_);
                            v___x_5464_ = leanh::lean_box(0);
                            v_isShared_5465_ = v_isSharedCheck_5469_;
                            state = 59;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5448_);
                    leanh::lean_dec(v_val_5446_);
                    leanh::lean_dec(v_val_5440_);
                    leanh::lean_dec_ref_known(v_a_5430_, 1);
                    leanh::lean_dec_ref(v_arg_5100_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5470_ = leanh::lean_box(0);
                    if v_isShared_5451_ == 0 {
                        leanh::lean_ctor_set(v___x_5450_, 0, v___x_5470_);
                        v___x_5472_ = v___x_5450_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_5473_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5470_);
                        v___x_5472_ = v_reuseFailAlloc_5473_;
                        state = 61;
                        continue;
                    }
                }
            }
            57 => {
                if v_isShared_5456_ == 0 {
                    leanh::lean_ctor_set(v___x_5455_, 0, v_a_5430_);
                    v___x_5458_ = v___x_5455_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_5459_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5430_);
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
                    v_reuseFailAlloc_5468_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5468_, 0, v_a_5462_);
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
                    v_reuseFailAlloc_5491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
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
                if leanh::lean_obj_tag(v_a_5502_) == 1 {
                    leanh::lean_del_object(v___x_5504_);
                    v_val_5506_ = leanh::lean_ctor_get(v_a_5502_, 0);
                    leanh::lean_inc(v_val_5506_);
                    leanh::lean_dec_ref_known(v_a_5502_, 1);
                    v___f_5507_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82;
                    v___x_5508_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11;
                    v___x_5509_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84;
                    v___x_5510_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_5506_, v_arg_5088_, v___f_5507_, v___x_5508_, v___x_5509_, v_origExpr_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                    return v___x_5510_;
                } else {
                    leanh::lean_dec(v_a_5502_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5511_ = leanh::lean_box(0);
                    if v_isShared_5505_ == 0 {
                        leanh::lean_ctor_set(v___x_5504_, 0, v___x_5511_);
                        v___x_5513_ = v___x_5504_;
                        state = 68;
                        continue;
                    } else {
                        v_reuseFailAlloc_5514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5511_);
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
                    v_reuseFailAlloc_5522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_a_5516_);
                    v___x_5521_ = v_reuseFailAlloc_5522_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_5521_;
            }
            71 => {
                if leanh::lean_obj_tag(v_a_5525_) == 1 {
                    leanh::lean_del_object(v___x_5527_);
                    v_val_5529_ = leanh::lean_ctor_get(v_a_5525_, 0);
                    leanh::lean_inc(v_val_5529_);
                    leanh::lean_dec_ref_known(v_a_5525_, 1);
                    v___x_5530_ = l_Lean_Meta_getNatValue_x3f(
                        v_arg_5088_,
                        v_a_5060_,
                        v_a_5061_,
                        v_a_5062_,
                        v_a_5063_,
                    );
                    leanh::lean_dec_ref(v_arg_5088_);
                    if leanh::lean_obj_tag(v___x_5530_) == 0 {
                        v_a_5531_ = leanh::lean_ctor_get(v___x_5530_, 0);
                        v_isSharedCheck_5580_ =
                            (!leanh::lean_is_exclusive(v___x_5530_)) as u8;
                        if v_isSharedCheck_5580_ == 0 {
                            v___x_5533_ = v___x_5530_;
                            v_isShared_5534_ = v_isSharedCheck_5580_;
                            state = 72;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5531_);
                            leanh::lean_dec(v___x_5530_);
                            v___x_5533_ = leanh::lean_box(0);
                            v_isShared_5534_ = v_isSharedCheck_5580_;
                            state = 72;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_5529_);
                        leanh::lean_dec_ref(v_arg_5085_);
                        leanh::lean_dec_ref(v_origExpr_5057_);
                        v_a_5581_ = leanh::lean_ctor_get(v___x_5530_, 0);
                        v_isSharedCheck_5588_ =
                            (!leanh::lean_is_exclusive(v___x_5530_)) as u8;
                        if v_isSharedCheck_5588_ == 0 {
                            v___x_5583_ = v___x_5530_;
                            v_isShared_5584_ = v_isSharedCheck_5588_;
                            state = 80;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5581_);
                            leanh::lean_dec(v___x_5530_);
                            v___x_5583_ = leanh::lean_box(0);
                            v_isShared_5584_ = v_isSharedCheck_5588_;
                            state = 80;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_5525_);
                    leanh::lean_dec_ref(v_arg_5088_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5589_ = leanh::lean_box(0);
                    if v_isShared_5528_ == 0 {
                        leanh::lean_ctor_set(v___x_5527_, 0, v___x_5589_);
                        v___x_5591_ = v___x_5527_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_5592_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5592_, 0, v___x_5589_);
                        v___x_5591_ = v_reuseFailAlloc_5592_;
                        state = 82;
                        continue;
                    }
                }
            }
            72 => {
                if leanh::lean_obj_tag(v_a_5531_) == 1 {
                    leanh::lean_del_object(v___x_5533_);
                    v_val_5535_ = leanh::lean_ctor_get(v_a_5531_, 0);
                    v_isSharedCheck_5575_ = (!leanh::lean_is_exclusive(v_a_5531_)) as u8;
                    if v_isSharedCheck_5575_ == 0 {
                        v___x_5537_ = v_a_5531_;
                        v_isShared_5538_ = v_isSharedCheck_5575_;
                        state = 73;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5535_);
                        leanh::lean_dec(v_a_5531_);
                        v___x_5537_ = leanh::lean_box(0);
                        v_isShared_5538_ = v_isSharedCheck_5575_;
                        state = 73;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5531_);
                    leanh::lean_dec(v_val_5529_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v___x_5576_ = leanh::lean_box(0);
                    if v_isShared_5534_ == 0 {
                        leanh::lean_ctor_set(v___x_5533_, 0, v___x_5576_);
                        v___x_5578_ = v___x_5533_;
                        state = 79;
                        continue;
                    } else {
                        v_reuseFailAlloc_5579_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5576_);
                        v___x_5578_ = v_reuseFailAlloc_5579_;
                        state = 79;
                        continue;
                    }
                }
            }
            73 => {
                v_width_5539_ = leanh::lean_ctor_get(v_val_5529_, 0);
                leanh::lean_inc_n(v_width_5539_, 2);
                v_bvExpr_5540_ = leanh::lean_ctor_get(v_val_5529_, 1);
                v_expr_5541_ = leanh::lean_ctor_get(v_val_5529_, 4);
                leanh::lean_inc_ref(v_expr_5541_);
                v___x_5542_ = lean_nat_mul(v_width_5539_, v_val_5535_);
                leanh::lean_inc_ref(v_bvExpr_5540_);
                leanh::lean_inc(v_val_5535_);
                leanh::lean_inc_n(v___x_5542_, 2);
                v___x_5543_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(
                    v_width_5539_,
                    v___x_5542_,
                    v_val_5535_,
                    v_bvExpr_5540_,
                );
                v___x_5544_ = l_Lean_mkNatLit(v___x_5542_);
                leanh::lean_inc_ref(v___x_5544_);
                v___x_5545_ =
                    l_Lean_Meta_mkEqRefl(v___x_5544_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_);
                if leanh::lean_obj_tag(v___x_5545_) == 0 {
                    v_a_5546_ = leanh::lean_ctor_get(v___x_5545_, 0);
                    v_isSharedCheck_5566_ = (!leanh::lean_is_exclusive(v___x_5545_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v___x_5548_ = v___x_5545_;
                        v_isShared_5549_ = v_isSharedCheck_5566_;
                        state = 74;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5546_);
                        leanh::lean_dec(v___x_5545_);
                        v___x_5548_ = leanh::lean_box(0);
                        v_isShared_5549_ = v_isSharedCheck_5566_;
                        state = 74;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_5544_);
                    leanh::lean_dec_ref(v___x_5543_);
                    leanh::lean_dec(v___x_5542_);
                    leanh::lean_dec_ref(v_expr_5541_);
                    leanh::lean_dec(v_width_5539_);
                    leanh::lean_del_object(v___x_5537_);
                    leanh::lean_dec(v_val_5535_);
                    leanh::lean_dec(v_val_5529_);
                    leanh::lean_dec_ref(v_arg_5085_);
                    leanh::lean_dec_ref(v_origExpr_5057_);
                    v_a_5567_ = leanh::lean_ctor_get(v___x_5545_, 0);
                    v_isSharedCheck_5574_ = (!leanh::lean_is_exclusive(v___x_5545_)) as u8;
                    if v_isSharedCheck_5574_ == 0 {
                        v___x_5569_ = v___x_5545_;
                        v_isShared_5570_ = v_isSharedCheck_5574_;
                        state = 77;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5567_);
                        leanh::lean_dec(v___x_5545_);
                        v___x_5569_ = leanh::lean_box(0);
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
                v___x_5553_ = leanh::lean_box(0);
                v___x_5554_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_once), _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86);
                leanh::lean_inc(v_width_5539_);
                v___x_5555_ = l_Lean_mkNatLit(v_width_5539_);
                v___x_5556_ = l_Lean_mkNatLit(v_val_5535_);
                leanh::lean_inc_ref(v___x_5555_);
                leanh::lean_inc_ref(v___x_5556_);
                leanh::lean_inc_ref(v_expr_5541_);
                v___f_5557_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed as *mut core::ffi::c_void, 17, 11);
                leanh::lean_closure_set(v___f_5557_, 0, v_width_5539_);
                leanh::lean_closure_set(v___f_5557_, 1, v_expr_5541_);
                leanh::lean_closure_set(v___f_5557_, 2, v_val_5529_);
                leanh::lean_closure_set(v___f_5557_, 3, v___x_5550_);
                leanh::lean_closure_set(v___f_5557_, 4, v___x_5551_);
                leanh::lean_closure_set(v___f_5557_, 5, v___x_5552_);
                leanh::lean_closure_set(v___f_5557_, 6, v___x_5090_);
                leanh::lean_closure_set(v___f_5557_, 7, v___x_5553_);
                leanh::lean_closure_set(v___f_5557_, 8, v___x_5556_);
                leanh::lean_closure_set(v___f_5557_, 9, v___x_5555_);
                leanh::lean_closure_set(v___f_5557_, 10, v_arg_5085_);
                v___x_5558_ = l_Lean_mkApp5(
                    v___x_5554_,
                    v___x_5555_,
                    v___x_5544_,
                    v___x_5556_,
                    v_expr_5541_,
                    v_a_5546_,
                );
                v___x_5559_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_5559_, 0, v___x_5542_);
                leanh::lean_ctor_set(v___x_5559_, 1, v___x_5543_);
                leanh::lean_ctor_set(v___x_5559_, 2, v_origExpr_5057_);
                leanh::lean_ctor_set(v___x_5559_, 3, v___f_5557_);
                leanh::lean_ctor_set(v___x_5559_, 4, v___x_5558_);
                if v_isShared_5538_ == 0 {
                    leanh::lean_ctor_set(v___x_5537_, 0, v___x_5559_);
                    v___x_5561_ = v___x_5537_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5565_, 0, v___x_5559_);
                    v___x_5561_ = v_reuseFailAlloc_5565_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                if v_isShared_5549_ == 0 {
                    leanh::lean_ctor_set(v___x_5548_, 0, v___x_5561_);
                    v___x_5563_ = v___x_5548_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_5564_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5561_);
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
                    v_reuseFailAlloc_5573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_a_5567_);
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
                    v_reuseFailAlloc_5587_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
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
                    v_reuseFailAlloc_5619_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
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
                    v_reuseFailAlloc_5627_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
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
    mut v_e_5629_: *mut leanh::LeanObject,
    mut v_a_5630_: *mut leanh::LeanObject,
    mut v_a_5631_: *mut leanh::LeanObject,
    mut v_a_5632_: *mut leanh::LeanObject,
    mut v_a_5633_: *mut leanh::LeanObject,
    mut v_a_5634_: *mut leanh::LeanObject,
    mut v_a_5635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvPredCache_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvLogicalCache_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5650_: u8 = 0;
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v___x_5661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bvExprCache_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5671_: u8 = 0;
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5661_ = lean_st_ref_get(v_a_5630_);
                v_bvExprCache_5662_ = leanh::lean_ctor_get(v___x_5661_, 1);
                leanh::lean_inc_ref(v_bvExprCache_5662_);
                leanh::lean_dec(v___x_5661_);
                v___x_5663_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvExprCache_5662_, v_e_5629_);
                leanh::lean_dec_ref(v_bvExprCache_5662_);
                if leanh::lean_obj_tag(v___x_5663_) == 0 {
                    leanh::lean_inc_ref(v_e_5629_);
                    v___x_5664_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_e_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_);
                    if leanh::lean_obj_tag(v___x_5664_) == 0 {
                        v_a_5665_ = leanh::lean_ctor_get(v___x_5664_, 0);
                        leanh::lean_inc(v_a_5665_);
                        if leanh::lean_obj_tag(v_a_5665_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5664_, 1);
                            v___x_5666_ = 0;
                            leanh::lean_inc_ref(v_e_5629_);
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
                            leanh::lean_dec_ref_known(v_a_5665_, 1);
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
                    leanh::lean_dec_ref(v_e_5629_);
                    v_val_5668_ = leanh::lean_ctor_get(v___x_5663_, 0);
                    v_isSharedCheck_5675_ = (!leanh::lean_is_exclusive(v___x_5663_)) as u8;
                    if v_isSharedCheck_5675_ == 0 {
                        v___x_5670_ = v___x_5663_;
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5668_);
                        leanh::lean_dec(v___x_5663_);
                        v___x_5670_ = leanh::lean_box(0);
                        v_isShared_5671_ = v_isSharedCheck_5675_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_5638_) == 0 {
                    v_a_5639_ = leanh::lean_ctor_get(v___y_5638_, 0);
                    v_isSharedCheck_5660_ = (!leanh::lean_is_exclusive(v___y_5638_)) as u8;
                    if v_isSharedCheck_5660_ == 0 {
                        v___x_5641_ = v___y_5638_;
                        v_isShared_5642_ = v_isSharedCheck_5660_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5639_);
                        leanh::lean_dec(v___y_5638_);
                        v___x_5641_ = leanh::lean_box(0);
                        v_isShared_5642_ = v_isSharedCheck_5660_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5629_);
                    return v___y_5638_;
                }
            }
            2 => {
                v___x_5643_ = lean_st_ref_take(v_a_5630_);
                v_lemmas_5644_ = leanh::lean_ctor_get(v___x_5643_, 0);
                v_bvExprCache_5645_ = leanh::lean_ctor_get(v___x_5643_, 1);
                v_bvPredCache_5646_ = leanh::lean_ctor_get(v___x_5643_, 2);
                v_bvLogicalCache_5647_ = leanh::lean_ctor_get(v___x_5643_, 3);
                v_isSharedCheck_5659_ = (!leanh::lean_is_exclusive(v___x_5643_)) as u8;
                if v_isSharedCheck_5659_ == 0 {
                    v___x_5649_ = v___x_5643_;
                    v_isShared_5650_ = v_isSharedCheck_5659_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_bvLogicalCache_5647_);
                    leanh::lean_inc(v_bvPredCache_5646_);
                    leanh::lean_inc(v_bvExprCache_5645_);
                    leanh::lean_inc(v_lemmas_5644_);
                    leanh::lean_dec(v___x_5643_);
                    v___x_5649_ = leanh::lean_box(0);
                    v_isShared_5650_ = v_isSharedCheck_5659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc(v_a_5639_);
                v___x_5651_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvExprCache_5645_, v_e_5629_, v_a_5639_);
                if v_isShared_5650_ == 0 {
                    leanh::lean_ctor_set(v___x_5649_, 1, v___x_5651_);
                    v___x_5653_ = v___x_5649_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5658_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_lemmas_5644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 1, v___x_5651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 2, v_bvPredCache_5646_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 3, v_bvLogicalCache_5647_);
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
                    v_reuseFailAlloc_5657_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5639_);
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
                    leanh::lean_ctor_set_tag(v___x_5670_, 0);
                    v___x_5673_ = v___x_5670_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5674_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_val_5668_);
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
    mut v_origExpr_5676_: *mut leanh::LeanObject,
    mut v_a_5677_: *mut leanh::LeanObject,
    mut v_a_5678_: *mut leanh::LeanObject,
    mut v_a_5679_: *mut leanh::LeanObject,
    mut v_a_5680_: *mut leanh::LeanObject,
    mut v_a_5681_: *mut leanh::LeanObject,
    mut v_a_5682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5684_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_origExpr_5676_, v_a_5677_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_, v_a_5682_);
    return v___x_5684_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
    mut v_origExpr_5685_: *mut leanh::LeanObject,
    mut v_a_5686_: *mut leanh::LeanObject,
    mut v_a_5687_: *mut leanh::LeanObject,
    mut v_a_5688_: *mut leanh::LeanObject,
    mut v_a_5689_: *mut leanh::LeanObject,
    mut v_a_5690_: *mut leanh::LeanObject,
    mut v_a_5691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5693_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_);
    return v___x_5693_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of___boxed(
    mut v_origExpr_5694_: *mut leanh::LeanObject,
    mut v_a_5695_: *mut leanh::LeanObject,
    mut v_a_5696_: *mut leanh::LeanObject,
    mut v_a_5697_: *mut leanh::LeanObject,
    mut v_a_5698_: *mut leanh::LeanObject,
    mut v_a_5699_: *mut leanh::LeanObject,
    mut v_a_5700_: *mut leanh::LeanObject,
    mut v_a_5701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5702_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(
        v_origExpr_5694_,
        v_a_5695_,
        v_a_5696_,
        v_a_5697_,
        v_a_5698_,
        v_a_5699_,
        v_a_5700_,
    );
    leanh::lean_dec(v_a_5700_);
    leanh::lean_dec_ref(v_a_5699_);
    leanh::lean_dec(v_a_5698_);
    leanh::lean_dec_ref(v_a_5697_);
    leanh::lean_dec(v_a_5696_);
    leanh::lean_dec(v_a_5695_);
    return v_res_5702_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of___boxed(
    mut v_origExpr_5703_: *mut leanh::LeanObject,
    mut v_a_5704_: *mut leanh::LeanObject,
    mut v_a_5705_: *mut leanh::LeanObject,
    mut v_a_5706_: *mut leanh::LeanObject,
    mut v_a_5707_: *mut leanh::LeanObject,
    mut v_a_5708_: *mut leanh::LeanObject,
    mut v_a_5709_: *mut leanh::LeanObject,
    mut v_a_5710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5711_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(
        v_origExpr_5703_,
        v_a_5704_,
        v_a_5705_,
        v_a_5706_,
        v_a_5707_,
        v_a_5708_,
        v_a_5709_,
    );
    leanh::lean_dec(v_a_5709_);
    leanh::lean_dec_ref(v_a_5708_);
    leanh::lean_dec(v_a_5707_);
    leanh::lean_dec_ref(v_a_5706_);
    leanh::lean_dec(v_a_5705_);
    leanh::lean_dec(v_a_5704_);
    return v_res_5711_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of___boxed(
    mut v_origExpr_5712_: *mut leanh::LeanObject,
    mut v_a_5713_: *mut leanh::LeanObject,
    mut v_a_5714_: *mut leanh::LeanObject,
    mut v_a_5715_: *mut leanh::LeanObject,
    mut v_a_5716_: *mut leanh::LeanObject,
    mut v_a_5717_: *mut leanh::LeanObject,
    mut v_a_5718_: *mut leanh::LeanObject,
    mut v_a_5719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5720_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(
        v_origExpr_5712_,
        v_a_5713_,
        v_a_5714_,
        v_a_5715_,
        v_a_5716_,
        v_a_5717_,
        v_a_5718_,
    );
    leanh::lean_dec(v_a_5718_);
    leanh::lean_dec_ref(v_a_5717_);
    leanh::lean_dec(v_a_5716_);
    leanh::lean_dec_ref(v_a_5715_);
    leanh::lean_dec(v_a_5714_);
    leanh::lean_dec(v_a_5713_);
    return v_res_5720_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom___boxed(
    mut v_origExpr_5721_: *mut leanh::LeanObject,
    mut v_a_5722_: *mut leanh::LeanObject,
    mut v_a_5723_: *mut leanh::LeanObject,
    mut v_a_5724_: *mut leanh::LeanObject,
    mut v_a_5725_: *mut leanh::LeanObject,
    mut v_a_5726_: *mut leanh::LeanObject,
    mut v_a_5727_: *mut leanh::LeanObject,
    mut v_a_5728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5729_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_5721_, v_a_5722_, v_a_5723_, v_a_5724_, v_a_5725_, v_a_5726_, v_a_5727_);
    leanh::lean_dec(v_a_5727_);
    leanh::lean_dec_ref(v_a_5726_);
    leanh::lean_dec(v_a_5725_);
    leanh::lean_dec_ref(v_a_5724_);
    leanh::lean_dec(v_a_5723_);
    leanh::lean_dec(v_a_5722_);
    return v_res_5729_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom___boxed(
    mut v_origExpr_5730_: *mut leanh::LeanObject,
    mut v_a_5731_: *mut leanh::LeanObject,
    mut v_a_5732_: *mut leanh::LeanObject,
    mut v_a_5733_: *mut leanh::LeanObject,
    mut v_a_5734_: *mut leanh::LeanObject,
    mut v_a_5735_: *mut leanh::LeanObject,
    mut v_a_5736_: *mut leanh::LeanObject,
    mut v_a_5737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5738_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_5730_, v_a_5731_, v_a_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_);
    leanh::lean_dec(v_a_5736_);
    leanh::lean_dec_ref(v_a_5735_);
    leanh::lean_dec(v_a_5734_);
    leanh::lean_dec_ref(v_a_5733_);
    leanh::lean_dec(v_a_5732_);
    leanh::lean_dec(v_a_5731_);
    return v_res_5738_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection___boxed(
    mut v_distanceExpr_5739_: *mut leanh::LeanObject,
    mut v_innerExpr_5740_: *mut leanh::LeanObject,
    mut v_rotateOp_5741_: *mut leanh::LeanObject,
    mut v_rotateOpName_5742_: *mut leanh::LeanObject,
    mut v_congrThm_5743_: *mut leanh::LeanObject,
    mut v_origExpr_5744_: *mut leanh::LeanObject,
    mut v_a_5745_: *mut leanh::LeanObject,
    mut v_a_5746_: *mut leanh::LeanObject,
    mut v_a_5747_: *mut leanh::LeanObject,
    mut v_a_5748_: *mut leanh::LeanObject,
    mut v_a_5749_: *mut leanh::LeanObject,
    mut v_a_5750_: *mut leanh::LeanObject,
    mut v_a_5751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5752_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_distanceExpr_5739_, v_innerExpr_5740_, v_rotateOp_5741_, v_rotateOpName_5742_, v_congrThm_5743_, v_origExpr_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_);
    leanh::lean_dec(v_a_5750_);
    leanh::lean_dec_ref(v_a_5749_);
    leanh::lean_dec(v_a_5748_);
    leanh::lean_dec_ref(v_a_5747_);
    leanh::lean_dec(v_a_5746_);
    leanh::lean_dec(v_a_5745_);
    leanh::lean_dec_ref(v_distanceExpr_5739_);
    return v_res_5752_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred___boxed(
    mut v_origExpr_5753_: *mut leanh::LeanObject,
    mut v_a_5754_: *mut leanh::LeanObject,
    mut v_a_5755_: *mut leanh::LeanObject,
    mut v_a_5756_: *mut leanh::LeanObject,
    mut v_a_5757_: *mut leanh::LeanObject,
    mut v_a_5758_: *mut leanh::LeanObject,
    mut v_a_5759_: *mut leanh::LeanObject,
    mut v_a_5760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5761_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_5753_, v_a_5754_, v_a_5755_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
    leanh::lean_dec(v_a_5759_);
    leanh::lean_dec_ref(v_a_5758_);
    leanh::lean_dec(v_a_5757_);
    leanh::lean_dec_ref(v_a_5756_);
    leanh::lean_dec(v_a_5755_);
    leanh::lean_dec(v_a_5754_);
    return v_res_5761_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection___boxed(
    mut v_lhsExpr_5762_: *mut leanh::LeanObject,
    mut v_rhsExpr_5763_: *mut leanh::LeanObject,
    mut v_pred_5764_: *mut leanh::LeanObject,
    mut v_origExpr_5765_: *mut leanh::LeanObject,
    mut v_a_5766_: *mut leanh::LeanObject,
    mut v_a_5767_: *mut leanh::LeanObject,
    mut v_a_5768_: *mut leanh::LeanObject,
    mut v_a_5769_: *mut leanh::LeanObject,
    mut v_a_5770_: *mut leanh::LeanObject,
    mut v_a_5771_: *mut leanh::LeanObject,
    mut v_a_5772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pred_boxed_5773_: u8 = 0;
    let mut v_res_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pred_boxed_5773_ = (leanh::lean_unbox(v_pred_5764_) as u8);
    v_res_5774_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_lhsExpr_5762_, v_rhsExpr_5763_, v_pred_boxed_5773_, v_origExpr_5765_, v_a_5766_, v_a_5767_, v_a_5768_, v_a_5769_, v_a_5770_, v_a_5771_);
    leanh::lean_dec(v_a_5771_);
    leanh::lean_dec_ref(v_a_5770_);
    leanh::lean_dec(v_a_5769_);
    leanh::lean_dec_ref(v_a_5768_);
    leanh::lean_dec(v_a_5767_);
    leanh::lean_dec(v_a_5766_);
    return v_res_5774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection___boxed(
    mut v_lhsExpr_5775_: *mut leanh::LeanObject,
    mut v_rhsExpr_5776_: *mut leanh::LeanObject,
    mut v_gate_5777_: *mut leanh::LeanObject,
    mut v_origExpr_5778_: *mut leanh::LeanObject,
    mut v_a_5779_: *mut leanh::LeanObject,
    mut v_a_5780_: *mut leanh::LeanObject,
    mut v_a_5781_: *mut leanh::LeanObject,
    mut v_a_5782_: *mut leanh::LeanObject,
    mut v_a_5783_: *mut leanh::LeanObject,
    mut v_a_5784_: *mut leanh::LeanObject,
    mut v_a_5785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_gate_boxed_5786_: u8 = 0;
    let mut v_res_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_gate_boxed_5786_ = (leanh::lean_unbox(v_gate_5777_) as u8);
    v_res_5787_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_lhsExpr_5775_, v_rhsExpr_5776_, v_gate_boxed_5786_, v_origExpr_5778_, v_a_5779_, v_a_5780_, v_a_5781_, v_a_5782_, v_a_5783_, v_a_5784_);
    leanh::lean_dec(v_a_5784_);
    leanh::lean_dec_ref(v_a_5783_);
    leanh::lean_dec(v_a_5782_);
    leanh::lean_dec_ref(v_a_5781_);
    leanh::lean_dec(v_a_5780_);
    leanh::lean_dec(v_a_5779_);
    return v_res_5787_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(
    mut v_distance_5788_: *mut leanh::LeanObject,
    mut v_innerExpr_5789_: *mut leanh::LeanObject,
    mut v_shiftOp_5790_: *mut leanh::LeanObject,
    mut v_shiftOpName_5791_: *mut leanh::LeanObject,
    mut v_congrThm_5792_: *mut leanh::LeanObject,
    mut v_origExpr_5793_: *mut leanh::LeanObject,
    mut v_a_5794_: *mut leanh::LeanObject,
    mut v_a_5795_: *mut leanh::LeanObject,
    mut v_a_5796_: *mut leanh::LeanObject,
    mut v_a_5797_: *mut leanh::LeanObject,
    mut v_a_5798_: *mut leanh::LeanObject,
    mut v_a_5799_: *mut leanh::LeanObject,
    mut v_a_5800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5801_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_distance_5788_, v_innerExpr_5789_, v_shiftOp_5790_, v_shiftOpName_5791_, v_congrThm_5792_, v_origExpr_5793_, v_a_5794_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_, v_a_5799_);
    leanh::lean_dec(v_a_5799_);
    leanh::lean_dec_ref(v_a_5798_);
    leanh::lean_dec(v_a_5797_);
    leanh::lean_dec_ref(v_a_5796_);
    leanh::lean_dec(v_a_5795_);
    leanh::lean_dec(v_a_5794_);
    return v_res_5801_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection___boxed(
    mut v_distanceExpr_5802_: *mut leanh::LeanObject,
    mut v_innerExpr_5803_: *mut leanh::LeanObject,
    mut v_shiftOp_5804_: *mut leanh::LeanObject,
    mut v_shiftOpName_5805_: *mut leanh::LeanObject,
    mut v_congrThm_5806_: *mut leanh::LeanObject,
    mut v_origExpr_5807_: *mut leanh::LeanObject,
    mut v_a_5808_: *mut leanh::LeanObject,
    mut v_a_5809_: *mut leanh::LeanObject,
    mut v_a_5810_: *mut leanh::LeanObject,
    mut v_a_5811_: *mut leanh::LeanObject,
    mut v_a_5812_: *mut leanh::LeanObject,
    mut v_a_5813_: *mut leanh::LeanObject,
    mut v_a_5814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5815_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_distanceExpr_5802_, v_innerExpr_5803_, v_shiftOp_5804_, v_shiftOpName_5805_, v_congrThm_5806_, v_origExpr_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_);
    leanh::lean_dec(v_a_5813_);
    leanh::lean_dec_ref(v_a_5812_);
    leanh::lean_dec(v_a_5811_);
    leanh::lean_dec_ref(v_a_5810_);
    leanh::lean_dec(v_a_5809_);
    leanh::lean_dec(v_a_5808_);
    return v_res_5815_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(
    mut v_e_5816_: *mut leanh::LeanObject,
    mut v_a_5817_: *mut leanh::LeanObject,
    mut v_a_5818_: *mut leanh::LeanObject,
    mut v_a_5819_: *mut leanh::LeanObject,
    mut v_a_5820_: *mut leanh::LeanObject,
    mut v_a_5821_: *mut leanh::LeanObject,
    mut v_a_5822_: *mut leanh::LeanObject,
    mut v_a_5823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5824_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_e_5816_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_, v_a_5821_, v_a_5822_);
    leanh::lean_dec(v_a_5822_);
    leanh::lean_dec_ref(v_a_5821_);
    leanh::lean_dec(v_a_5820_);
    leanh::lean_dec_ref(v_a_5819_);
    leanh::lean_dec(v_a_5818_);
    leanh::lean_dec(v_a_5817_);
    return v_res_5824_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5___boxed(
    mut v_e_5825_: *mut leanh::LeanObject,
    mut v_a_5826_: *mut leanh::LeanObject,
    mut v_a_5827_: *mut leanh::LeanObject,
    mut v_a_5828_: *mut leanh::LeanObject,
    mut v_a_5829_: *mut leanh::LeanObject,
    mut v_a_5830_: *mut leanh::LeanObject,
    mut v_a_5831_: *mut leanh::LeanObject,
    mut v_a_5832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5833_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(v_e_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_, v_a_5830_, v_a_5831_);
    leanh::lean_dec(v_a_5831_);
    leanh::lean_dec_ref(v_a_5830_);
    leanh::lean_dec(v_a_5829_);
    leanh::lean_dec_ref(v_a_5828_);
    leanh::lean_dec(v_a_5827_);
    leanh::lean_dec(v_a_5826_);
    return v_res_5833_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(
    mut v_e_5834_: *mut leanh::LeanObject,
    mut v_a_5835_: *mut leanh::LeanObject,
    mut v_a_5836_: *mut leanh::LeanObject,
    mut v_a_5837_: *mut leanh::LeanObject,
    mut v_a_5838_: *mut leanh::LeanObject,
    mut v_a_5839_: *mut leanh::LeanObject,
    mut v_a_5840_: *mut leanh::LeanObject,
    mut v_a_5841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5842_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_e_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_);
    leanh::lean_dec(v_a_5840_);
    leanh::lean_dec_ref(v_a_5839_);
    leanh::lean_dec(v_a_5838_);
    leanh::lean_dec_ref(v_a_5837_);
    leanh::lean_dec(v_a_5836_);
    leanh::lean_dec(v_a_5835_);
    return v_res_5842_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___boxed(
    mut v_innerExpr_5843_: *mut leanh::LeanObject,
    mut v_op_5844_: *mut leanh::LeanObject,
    mut v_congrThm_5845_: *mut leanh::LeanObject,
    mut v_origExpr_5846_: *mut leanh::LeanObject,
    mut v_a_5847_: *mut leanh::LeanObject,
    mut v_a_5848_: *mut leanh::LeanObject,
    mut v_a_5849_: *mut leanh::LeanObject,
    mut v_a_5850_: *mut leanh::LeanObject,
    mut v_a_5851_: *mut leanh::LeanObject,
    mut v_a_5852_: *mut leanh::LeanObject,
    mut v_a_5853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5854_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_innerExpr_5843_, v_op_5844_, v_congrThm_5845_, v_origExpr_5846_, v_a_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_, v_a_5852_);
    leanh::lean_dec(v_a_5852_);
    leanh::lean_dec_ref(v_a_5851_);
    leanh::lean_dec(v_a_5850_);
    leanh::lean_dec_ref(v_a_5849_);
    leanh::lean_dec(v_a_5848_);
    leanh::lean_dec(v_a_5847_);
    return v_res_5854_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___boxed(
    mut v_lhsExpr_5855_: *mut leanh::LeanObject,
    mut v_rhsExpr_5856_: *mut leanh::LeanObject,
    mut v_op_5857_: *mut leanh::LeanObject,
    mut v_congrThm_5858_: *mut leanh::LeanObject,
    mut v_origExpr_5859_: *mut leanh::LeanObject,
    mut v_a_5860_: *mut leanh::LeanObject,
    mut v_a_5861_: *mut leanh::LeanObject,
    mut v_a_5862_: *mut leanh::LeanObject,
    mut v_a_5863_: *mut leanh::LeanObject,
    mut v_a_5864_: *mut leanh::LeanObject,
    mut v_a_5865_: *mut leanh::LeanObject,
    mut v_a_5866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_boxed_5867_: u8 = 0;
    let mut v_res_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_op_boxed_5867_ = (leanh::lean_unbox(v_op_5857_) as u8);
    v_res_5868_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_lhsExpr_5855_, v_rhsExpr_5856_, v_op_boxed_5867_, v_congrThm_5858_, v_origExpr_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_, v_a_5865_);
    leanh::lean_dec(v_a_5865_);
    leanh::lean_dec_ref(v_a_5864_);
    leanh::lean_dec(v_a_5863_);
    leanh::lean_dec_ref(v_a_5862_);
    leanh::lean_dec(v_a_5861_);
    leanh::lean_dec(v_a_5860_);
    return v_res_5868_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___boxed(
    mut v_origExpr_5869_: *mut leanh::LeanObject,
    mut v_a_5870_: *mut leanh::LeanObject,
    mut v_a_5871_: *mut leanh::LeanObject,
    mut v_a_5872_: *mut leanh::LeanObject,
    mut v_a_5873_: *mut leanh::LeanObject,
    mut v_a_5874_: *mut leanh::LeanObject,
    mut v_a_5875_: *mut leanh::LeanObject,
    mut v_a_5876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5877_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_origExpr_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_);
    leanh::lean_dec(v_a_5875_);
    leanh::lean_dec_ref(v_a_5874_);
    leanh::lean_dec(v_a_5873_);
    leanh::lean_dec_ref(v_a_5872_);
    leanh::lean_dec(v_a_5871_);
    leanh::lean_dec(v_a_5870_);
    return v_res_5877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___boxed(
    mut v_origExpr_5878_: *mut leanh::LeanObject,
    mut v_a_5879_: *mut leanh::LeanObject,
    mut v_a_5880_: *mut leanh::LeanObject,
    mut v_a_5881_: *mut leanh::LeanObject,
    mut v_a_5882_: *mut leanh::LeanObject,
    mut v_a_5883_: *mut leanh::LeanObject,
    mut v_a_5884_: *mut leanh::LeanObject,
    mut v_a_5885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5886_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_origExpr_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_);
    leanh::lean_dec(v_a_5884_);
    leanh::lean_dec_ref(v_a_5883_);
    leanh::lean_dec(v_a_5882_);
    leanh::lean_dec_ref(v_a_5881_);
    leanh::lean_dec(v_a_5880_);
    leanh::lean_dec(v_a_5879_);
    return v_res_5886_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___boxed(
    mut v_origExpr_5887_: *mut leanh::LeanObject,
    mut v_a_5888_: *mut leanh::LeanObject,
    mut v_a_5889_: *mut leanh::LeanObject,
    mut v_a_5890_: *mut leanh::LeanObject,
    mut v_a_5891_: *mut leanh::LeanObject,
    mut v_a_5892_: *mut leanh::LeanObject,
    mut v_a_5893_: *mut leanh::LeanObject,
    mut v_a_5894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5895_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_origExpr_5887_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
    leanh::lean_dec(v_a_5893_);
    leanh::lean_dec_ref(v_a_5892_);
    leanh::lean_dec(v_a_5891_);
    leanh::lean_dec_ref(v_a_5890_);
    leanh::lean_dec(v_a_5889_);
    leanh::lean_dec(v_a_5888_);
    return v_res_5895_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12(
    mut v_00_u03b1_5896_: *mut leanh::LeanObject,
    mut v_msg_5897_: *mut leanh::LeanObject,
    mut v___y_5898_: *mut leanh::LeanObject,
    mut v___y_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
    mut v___y_5902_: *mut leanh::LeanObject,
    mut v___y_5903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5905_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_5897_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_);
    return v___x_5905_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___boxed(
    mut v_00_u03b1_5906_: *mut leanh::LeanObject,
    mut v_msg_5907_: *mut leanh::LeanObject,
    mut v___y_5908_: *mut leanh::LeanObject,
    mut v___y_5909_: *mut leanh::LeanObject,
    mut v___y_5910_: *mut leanh::LeanObject,
    mut v___y_5911_: *mut leanh::LeanObject,
    mut v___y_5912_: *mut leanh::LeanObject,
    mut v___y_5913_: *mut leanh::LeanObject,
    mut v___y_5914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5915_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12(v_00_u03b1_5906_, v_msg_5907_, v___y_5908_, v___y_5909_, v___y_5910_, v___y_5911_, v___y_5912_, v___y_5913_);
    leanh::lean_dec(v___y_5913_);
    leanh::lean_dec_ref(v___y_5912_);
    leanh::lean_dec(v___y_5911_);
    leanh::lean_dec_ref(v___y_5910_);
    leanh::lean_dec(v___y_5909_);
    leanh::lean_dec(v___y_5908_);
    return v_res_5915_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(
    mut v_00_u03b2_5916_: *mut leanh::LeanObject,
    mut v_m_5917_: *mut leanh::LeanObject,
    mut v_a_5918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5919_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_5917_, v_a_5918_);
    return v___x_5919_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(
    mut v_00_u03b2_5920_: *mut leanh::LeanObject,
    mut v_m_5921_: *mut leanh::LeanObject,
    mut v_a_5922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(v_00_u03b2_5920_, v_m_5921_, v_a_5922_);
    leanh::lean_dec_ref(v_a_5922_);
    leanh::lean_dec_ref(v_m_5921_);
    return v_res_5923_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(
    mut v_00_u03b2_5924_: *mut leanh::LeanObject,
    mut v_m_5925_: *mut leanh::LeanObject,
    mut v_a_5926_: *mut leanh::LeanObject,
    mut v_b_5927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5928_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_m_5925_, v_a_5926_, v_b_5927_);
    return v___x_5928_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(
    mut v_00_u03b2_5929_: *mut leanh::LeanObject,
    mut v_a_5930_: *mut leanh::LeanObject,
    mut v_x_5931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5932_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_5930_, v_x_5931_);
    return v___x_5932_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(
    mut v_00_u03b2_5933_: *mut leanh::LeanObject,
    mut v_a_5934_: *mut leanh::LeanObject,
    mut v_x_5935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5936_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(v_00_u03b2_5933_, v_a_5934_, v_x_5935_);
    leanh::lean_dec(v_x_5935_);
    leanh::lean_dec_ref(v_a_5934_);
    return v_res_5936_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(
    mut v_00_u03b2_5937_: *mut leanh::LeanObject,
    mut v_a_5938_: *mut leanh::LeanObject,
    mut v_x_5939_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5940_: u8 = 0;
    v___x_5940_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_5938_, v_x_5939_);
    return v___x_5940_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(
    mut v_00_u03b2_5941_: *mut leanh::LeanObject,
    mut v_a_5942_: *mut leanh::LeanObject,
    mut v_x_5943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5944_: u8 = 0;
    let mut v_r_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5944_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(v_00_u03b2_5941_, v_a_5942_, v_x_5943_);
    leanh::lean_dec(v_x_5943_);
    leanh::lean_dec_ref(v_a_5942_);
    v_r_5945_ = leanh::lean_box((v_res_5944_) as usize);
    return v_r_5945_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(
    mut v_00_u03b2_5946_: *mut leanh::LeanObject,
    mut v_data_5947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5948_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_data_5947_);
    return v___x_5948_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(
    mut v_00_u03b2_5949_: *mut leanh::LeanObject,
    mut v_a_5950_: *mut leanh::LeanObject,
    mut v_b_5951_: *mut leanh::LeanObject,
    mut v_x_5952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5953_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_5950_, v_b_5951_, v_x_5952_);
    return v___x_5953_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(
    mut v_00_u03b2_5954_: *mut leanh::LeanObject,
    mut v_i_5955_: *mut leanh::LeanObject,
    mut v_source_5956_: *mut leanh::LeanObject,
    mut v_target_5957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5958_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v_i_5955_, v_source_5956_, v_target_5957_);
    return v___x_5958_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(
    mut v_00_u03b2_5959_: *mut leanh::LeanObject,
    mut v_x_5960_: *mut leanh::LeanObject,
    mut v_x_5961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5962_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_x_5960_, v_x_5961_);
    return v___x_5962_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
}