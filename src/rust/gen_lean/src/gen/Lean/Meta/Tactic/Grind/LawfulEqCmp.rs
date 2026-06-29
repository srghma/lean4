// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.LawfulEqCmp
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.SynthInstance
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_grind_mk_eq_proof, lean_infer_type, lean_nat_add,
    lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isConstOf, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_isExprDefEq;
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_decLevel_x3f;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_getOrderingEqExpr___redArg;
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_isEqv___redArg,
    l_Lean_Meta_Grind_pushEqCore___redArg, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_getBinOp,
    runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
pub static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [76, 97, 119, 102, 117, 108, 69, 113, 67, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,10789130220087302960 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [79, 114, 100, 101, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__3_value) as *mut crate::leanh::LeanObject,5208578977668345058 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 113, 95, 111, 102, 95, 99, 111, 109, 112, 97, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject,15734321041234825264 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__1_value) as *mut crate::leanh::LeanObject,10789130220087302960 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__5_value) as *mut crate::leanh::LeanObject,14389872809212625859 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(
    mut v_op_650_: *mut crate::leanh::LeanObject,
    mut v_a_651_: *mut crate::leanh::LeanObject,
    mut v_a_652_: *mut crate::leanh::LeanObject,
    mut v_a_653_: *mut crate::leanh::LeanObject,
    mut v_a_654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: u8 = 0;
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v_binderType_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v_binderType_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_702_: u8 = 0;
    let mut v_val_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v_val_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_716_: u8 = 0;
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_731_: u8 = 0;
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut v_a_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_744_: u8 = 0;
    let mut v_a_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_748_: u8 = 0;
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut v_a_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_757_: u8 = 0;
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut v_a_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_770_: u8 = 0;
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_774_: u8 = 0;
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_783_: u8 = 0;
    let mut v_a_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut v_a_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_656_ = lean_st_ref_get(v_a_654_);
                v_env_657_ = crate::leanh::lean_ctor_get(v___x_656_, 0);
                crate::leanh::lean_inc_ref(v_env_657_);
                crate::leanh::lean_dec(v___x_656_);
                v___x_658_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__2;
                v___x_659_ = 1;
                v___x_660_ = l_Lean_Environment_contains(v_env_657_, v___x_658_, v___x_659_);
                if v___x_660_ == 0 {
                    crate::leanh::lean_dec_ref(v_op_650_);
                    v___x_661_ = crate::leanh::lean_box(0);
                    v___x_662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_662_, 0, v___x_661_);
                    return v___x_662_;
                } else {
                    crate::leanh::lean_inc(v_a_654_);
                    crate::leanh::lean_inc_ref(v_a_653_);
                    crate::leanh::lean_inc(v_a_652_);
                    crate::leanh::lean_inc_ref(v_a_651_);
                    crate::leanh::lean_inc_ref(v_op_650_);
                    v___x_663_ = lean_infer_type(v_op_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
                    if crate::leanh::lean_obj_tag(v___x_663_) == 0 {
                        v_a_664_ = crate::leanh::lean_ctor_get(v___x_663_, 0);
                        crate::leanh::lean_inc(v_a_664_);
                        crate::leanh::lean_dec_ref_known(v___x_663_, 1);
                        crate::leanh::lean_inc(v_a_654_);
                        crate::leanh::lean_inc_ref(v_a_653_);
                        crate::leanh::lean_inc(v_a_652_);
                        crate::leanh::lean_inc_ref(v_a_651_);
                        v___x_665_ = lean_whnf(v_a_664_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
                        if crate::leanh::lean_obj_tag(v___x_665_) == 0 {
                            v_a_666_ = crate::leanh::lean_ctor_get(v___x_665_, 0);
                            v_isSharedCheck_783_ =
                                (!crate::leanh::lean_is_exclusive(v___x_665_)) as u8;
                            if v_isSharedCheck_783_ == 0 {
                                v___x_668_ = v___x_665_;
                                v_isShared_669_ = v_isSharedCheck_783_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_666_);
                                crate::leanh::lean_dec(v___x_665_);
                                v___x_668_ = crate::leanh::lean_box(0);
                                v_isShared_669_ = v_isSharedCheck_783_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_op_650_);
                            v_a_784_ = crate::leanh::lean_ctor_get(v___x_665_, 0);
                            v_isSharedCheck_791_ =
                                (!crate::leanh::lean_is_exclusive(v___x_665_)) as u8;
                            if v_isSharedCheck_791_ == 0 {
                                v___x_786_ = v___x_665_;
                                v_isShared_787_ = v_isSharedCheck_791_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_784_);
                                crate::leanh::lean_dec(v___x_665_);
                                v___x_786_ = crate::leanh::lean_box(0);
                                v_isShared_787_ = v_isSharedCheck_791_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_op_650_);
                        v_a_792_ = crate::leanh::lean_ctor_get(v___x_663_, 0);
                        v_isSharedCheck_799_ = (!crate::leanh::lean_is_exclusive(v___x_663_)) as u8;
                        if v_isSharedCheck_799_ == 0 {
                            v___x_794_ = v___x_663_;
                            v_isShared_795_ = v_isSharedCheck_799_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_792_);
                            crate::leanh::lean_dec(v___x_663_);
                            v___x_794_ = crate::leanh::lean_box(0);
                            v_isShared_795_ = v_isSharedCheck_799_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_666_) == 7 {
                    v_binderType_670_ = crate::leanh::lean_ctor_get(v_a_666_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_670_);
                    v_body_671_ = crate::leanh::lean_ctor_get(v_a_666_, 2);
                    crate::leanh::lean_inc_ref(v_body_671_);
                    crate::leanh::lean_dec_ref_known(v_a_666_, 3);
                    v___x_672_ = l_Lean_Expr_hasLooseBVars(v_body_671_);
                    if v___x_672_ == 0 {
                        crate::leanh::lean_del_object(v___x_668_);
                        crate::leanh::lean_inc(v_a_654_);
                        crate::leanh::lean_inc_ref(v_a_653_);
                        crate::leanh::lean_inc(v_a_652_);
                        crate::leanh::lean_inc_ref(v_a_651_);
                        v___x_673_ = lean_whnf(v_body_671_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
                        if crate::leanh::lean_obj_tag(v___x_673_) == 0 {
                            v_a_674_ = crate::leanh::lean_ctor_get(v___x_673_, 0);
                            v_isSharedCheck_766_ =
                                (!crate::leanh::lean_is_exclusive(v___x_673_)) as u8;
                            if v_isSharedCheck_766_ == 0 {
                                v___x_676_ = v___x_673_;
                                v_isShared_677_ = v_isSharedCheck_766_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_674_);
                                crate::leanh::lean_dec(v___x_673_);
                                v___x_676_ = crate::leanh::lean_box(0);
                                v_isShared_677_ = v_isSharedCheck_766_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_binderType_670_);
                            crate::leanh::lean_dec_ref(v_op_650_);
                            v_a_767_ = crate::leanh::lean_ctor_get(v___x_673_, 0);
                            v_isSharedCheck_774_ =
                                (!crate::leanh::lean_is_exclusive(v___x_673_)) as u8;
                            if v_isSharedCheck_774_ == 0 {
                                v___x_769_ = v___x_673_;
                                v_isShared_770_ = v_isSharedCheck_774_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_767_);
                                crate::leanh::lean_dec(v___x_673_);
                                v___x_769_ = crate::leanh::lean_box(0);
                                v_isShared_770_ = v_isSharedCheck_774_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_671_);
                        crate::leanh::lean_dec_ref(v_binderType_670_);
                        crate::leanh::lean_dec_ref(v_op_650_);
                        v___x_775_ = crate::leanh::lean_box(0);
                        if v_isShared_669_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_775_);
                            v___x_777_ = v___x_668_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_778_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
                            v___x_777_ = v_reuseFailAlloc_778_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_666_);
                    crate::leanh::lean_dec_ref(v_op_650_);
                    v___x_779_ = crate::leanh::lean_box(0);
                    if v_isShared_669_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_779_);
                        v___x_781_ = v___x_668_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                        v___x_781_ = v_reuseFailAlloc_782_;
                        state = 23;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_674_) == 7 {
                    v_binderType_678_ = crate::leanh::lean_ctor_get(v_a_674_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_678_);
                    v_body_679_ = crate::leanh::lean_ctor_get(v_a_674_, 2);
                    crate::leanh::lean_inc_ref(v_body_679_);
                    crate::leanh::lean_dec_ref_known(v_a_674_, 3);
                    v___x_680_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__4;
                    v___x_681_ = l_Lean_Expr_isConstOf(v_body_679_, v___x_680_);
                    crate::leanh::lean_dec_ref(v_body_679_);
                    if v___x_681_ == 0 {
                        crate::leanh::lean_dec_ref(v_binderType_678_);
                        crate::leanh::lean_dec_ref(v_binderType_670_);
                        crate::leanh::lean_dec_ref(v_op_650_);
                        v___x_682_ = crate::leanh::lean_box(0);
                        if v_isShared_677_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_682_);
                            v___x_684_ = v___x_676_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_685_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
                            v___x_684_ = v_reuseFailAlloc_685_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_676_);
                        crate::leanh::lean_inc_ref(v_binderType_670_);
                        v___x_686_ = l_Lean_Meta_isExprDefEq(
                            v_binderType_670_,
                            v_binderType_678_,
                            v_a_651_,
                            v_a_652_,
                            v_a_653_,
                            v_a_654_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_686_) == 0 {
                            v_a_687_ = crate::leanh::lean_ctor_get(v___x_686_, 0);
                            v_isSharedCheck_753_ =
                                (!crate::leanh::lean_is_exclusive(v___x_686_)) as u8;
                            if v_isSharedCheck_753_ == 0 {
                                v___x_689_ = v___x_686_;
                                v_isShared_690_ = v_isSharedCheck_753_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_687_);
                                crate::leanh::lean_dec(v___x_686_);
                                v___x_689_ = crate::leanh::lean_box(0);
                                v_isShared_690_ = v_isSharedCheck_753_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_binderType_670_);
                            crate::leanh::lean_dec_ref(v_op_650_);
                            v_a_754_ = crate::leanh::lean_ctor_get(v___x_686_, 0);
                            v_isSharedCheck_761_ =
                                (!crate::leanh::lean_is_exclusive(v___x_686_)) as u8;
                            if v_isSharedCheck_761_ == 0 {
                                v___x_756_ = v___x_686_;
                                v_isShared_757_ = v_isSharedCheck_761_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_754_);
                                crate::leanh::lean_dec(v___x_686_);
                                v___x_756_ = crate::leanh::lean_box(0);
                                v_isShared_757_ = v_isSharedCheck_761_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_674_);
                    crate::leanh::lean_dec_ref(v_binderType_670_);
                    crate::leanh::lean_dec_ref(v_op_650_);
                    v___x_762_ = crate::leanh::lean_box(0);
                    if v_isShared_677_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_762_);
                        v___x_764_ = v___x_676_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
                        v___x_764_ = v_reuseFailAlloc_765_;
                        state = 19;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_684_;
            }
            4 => {
                v___x_691_ = (crate::leanh::lean_unbox(v_a_687_) as u8);
                crate::leanh::lean_dec(v_a_687_);
                if v___x_691_ == 0 {
                    crate::leanh::lean_dec_ref(v_binderType_670_);
                    crate::leanh::lean_dec_ref(v_op_650_);
                    v___x_692_ = crate::leanh::lean_box(0);
                    if v_isShared_690_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_692_);
                        v___x_694_ = v___x_689_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
                        v___x_694_ = v_reuseFailAlloc_695_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_689_);
                    crate::leanh::lean_inc_ref(v_binderType_670_);
                    v___x_696_ = l_Lean_Meta_getLevel(
                        v_binderType_670_,
                        v_a_651_,
                        v_a_652_,
                        v_a_653_,
                        v_a_654_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_696_) == 0 {
                        v_a_697_ = crate::leanh::lean_ctor_get(v___x_696_, 0);
                        crate::leanh::lean_inc(v_a_697_);
                        crate::leanh::lean_dec_ref_known(v___x_696_, 1);
                        v___x_698_ = l_Lean_Meta_decLevel_x3f(
                            v_a_697_, v_a_651_, v_a_652_, v_a_653_, v_a_654_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_698_) == 0 {
                            v_a_699_ = crate::leanh::lean_ctor_get(v___x_698_, 0);
                            v_isSharedCheck_736_ =
                                (!crate::leanh::lean_is_exclusive(v___x_698_)) as u8;
                            if v_isSharedCheck_736_ == 0 {
                                v___x_701_ = v___x_698_;
                                v_isShared_702_ = v_isSharedCheck_736_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_699_);
                                crate::leanh::lean_dec(v___x_698_);
                                v___x_701_ = crate::leanh::lean_box(0);
                                v_isShared_702_ = v_isSharedCheck_736_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_binderType_670_);
                            crate::leanh::lean_dec_ref(v_op_650_);
                            v_a_737_ = crate::leanh::lean_ctor_get(v___x_698_, 0);
                            v_isSharedCheck_744_ =
                                (!crate::leanh::lean_is_exclusive(v___x_698_)) as u8;
                            if v_isSharedCheck_744_ == 0 {
                                v___x_739_ = v___x_698_;
                                v_isShared_740_ = v_isSharedCheck_744_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_737_);
                                crate::leanh::lean_dec(v___x_698_);
                                v___x_739_ = crate::leanh::lean_box(0);
                                v_isShared_740_ = v_isSharedCheck_744_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_binderType_670_);
                        crate::leanh::lean_dec_ref(v_op_650_);
                        v_a_745_ = crate::leanh::lean_ctor_get(v___x_696_, 0);
                        v_isSharedCheck_752_ = (!crate::leanh::lean_is_exclusive(v___x_696_)) as u8;
                        if v_isSharedCheck_752_ == 0 {
                            v___x_747_ = v___x_696_;
                            v_isShared_748_ = v_isSharedCheck_752_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_745_);
                            crate::leanh::lean_dec(v___x_696_);
                            v___x_747_ = crate::leanh::lean_box(0);
                            v_isShared_748_ = v_isSharedCheck_752_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_694_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_699_) == 1 {
                    crate::leanh::lean_del_object(v___x_701_);
                    v_val_703_ = crate::leanh::lean_ctor_get(v_a_699_, 0);
                    crate::leanh::lean_inc(v_val_703_);
                    crate::leanh::lean_dec_ref_known(v_a_699_, 1);
                    v___x_704_ = crate::leanh::lean_box(0);
                    v___x_705_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_705_, 0, v_val_703_);
                    crate::leanh::lean_ctor_set(v___x_705_, 1, v___x_704_);
                    crate::leanh::lean_inc_ref(v___x_705_);
                    v___x_706_ = l_Lean_mkConst(v___x_658_, v___x_705_);
                    crate::leanh::lean_inc_ref(v_op_650_);
                    crate::leanh::lean_inc_ref(v_binderType_670_);
                    v___x_707_ = l_Lean_mkAppB(v___x_706_, v_binderType_670_, v_op_650_);
                    v___x_708_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_707_, v_a_651_, v_a_652_, v_a_653_, v_a_654_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_708_) == 0 {
                        v_a_709_ = crate::leanh::lean_ctor_get(v___x_708_, 0);
                        v_isSharedCheck_731_ = (!crate::leanh::lean_is_exclusive(v___x_708_)) as u8;
                        if v_isSharedCheck_731_ == 0 {
                            v___x_711_ = v___x_708_;
                            v_isShared_712_ = v_isSharedCheck_731_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_709_);
                            crate::leanh::lean_dec(v___x_708_);
                            v___x_711_ = crate::leanh::lean_box(0);
                            v_isShared_712_ = v_isSharedCheck_731_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_705_, 2);
                        crate::leanh::lean_dec_ref(v_binderType_670_);
                        crate::leanh::lean_dec_ref(v_op_650_);
                        return v___x_708_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_699_);
                    crate::leanh::lean_dec_ref(v_binderType_670_);
                    crate::leanh::lean_dec_ref(v_op_650_);
                    v___x_732_ = crate::leanh::lean_box(0);
                    if v_isShared_702_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_701_, 0, v___x_732_);
                        v___x_734_ = v___x_701_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
                        v___x_734_ = v_reuseFailAlloc_735_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_709_) == 1 {
                    v_val_713_ = crate::leanh::lean_ctor_get(v_a_709_, 0);
                    v_isSharedCheck_726_ = (!crate::leanh::lean_is_exclusive(v_a_709_)) as u8;
                    if v_isSharedCheck_726_ == 0 {
                        v___x_715_ = v_a_709_;
                        v_isShared_716_ = v_isSharedCheck_726_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_713_);
                        crate::leanh::lean_dec(v_a_709_);
                        v___x_715_ = crate::leanh::lean_box(0);
                        v_isShared_716_ = v_isSharedCheck_726_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_709_);
                    crate::leanh::lean_dec_ref_known(v___x_705_, 2);
                    crate::leanh::lean_dec_ref(v_binderType_670_);
                    crate::leanh::lean_dec_ref(v_op_650_);
                    v___x_727_ = crate::leanh::lean_box(0);
                    if v_isShared_712_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_711_, 0, v___x_727_);
                        v___x_729_ = v___x_711_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
                        v___x_729_ = v_reuseFailAlloc_730_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                v___x_717_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___closed__6;
                v___x_718_ = l_Lean_mkConst(v___x_717_, v___x_705_);
                v___x_719_ = l_Lean_mkApp3(v___x_718_, v_binderType_670_, v_op_650_, v_val_713_);
                if v_isShared_716_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_719_);
                    v___x_721_ = v___x_715_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_725_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
                    v___x_721_ = v_reuseFailAlloc_725_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_711_, 0, v___x_721_);
                    v___x_723_ = v___x_711_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
                    v___x_723_ = v_reuseFailAlloc_724_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_723_;
            }
            11 => {
                return v___x_729_;
            }
            12 => {
                return v___x_734_;
            }
            13 => {
                if v_isShared_740_ == 0 {
                    v___x_742_ = v___x_739_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
                    v___x_742_ = v_reuseFailAlloc_743_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_742_;
            }
            15 => {
                if v_isShared_748_ == 0 {
                    v___x_750_ = v___x_747_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
                    v___x_750_ = v_reuseFailAlloc_751_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_750_;
            }
            17 => {
                if v_isShared_757_ == 0 {
                    v___x_759_ = v___x_756_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
                    v___x_759_ = v_reuseFailAlloc_760_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_759_;
            }
            19 => {
                return v___x_764_;
            }
            20 => {
                if v_isShared_770_ == 0 {
                    v___x_772_ = v___x_769_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
                    v___x_772_ = v_reuseFailAlloc_773_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_772_;
            }
            22 => {
                return v___x_777_;
            }
            23 => {
                return v___x_781_;
            }
            24 => {
                if v_isShared_787_ == 0 {
                    v___x_789_ = v___x_786_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
                    v___x_789_ = v_reuseFailAlloc_790_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_789_;
            }
            26 => {
                if v_isShared_795_ == 0 {
                    v___x_797_ = v___x_794_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
                    v___x_797_ = v_reuseFailAlloc_798_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f___boxed(
    mut v_op_800_: *mut crate::leanh::LeanObject,
    mut v_a_801_: *mut crate::leanh::LeanObject,
    mut v_a_802_: *mut crate::leanh::LeanObject,
    mut v_a_803_: *mut crate::leanh::LeanObject,
    mut v_a_804_: *mut crate::leanh::LeanObject,
    mut v_a_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_806_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(v_op_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
    crate::leanh::lean_dec(v_a_804_);
    crate::leanh::lean_dec_ref(v_a_803_);
    crate::leanh::lean_dec(v_a_802_);
    crate::leanh::lean_dec_ref(v_a_801_);
    return v_res_806_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_807_: *mut crate::leanh::LeanObject,
    mut v_vals_808_: *mut crate::leanh::LeanObject,
    mut v_i_809_: *mut crate::leanh::LeanObject,
    mut v_k_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: u8 = 0;
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: u8 = 0;
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_811_ = lean_array_get_size(v_keys_807_);
                v___x_812_ = lean_nat_dec_lt(v_i_809_, v___x_811_);
                if v___x_812_ == 0 {
                    crate::leanh::lean_dec(v_i_809_);
                    v___x_813_ = crate::leanh::lean_box(0);
                    return v___x_813_;
                } else {
                    v_k_x27_814_ = lean_array_fget_borrowed(v_keys_807_, v_i_809_);
                    v___x_815_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_810_,
                            v_k_x27_814_,
                        );
                    if v___x_815_ == 0 {
                        v___x_816_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_817_ = lean_nat_add(v_i_809_, v___x_816_);
                        crate::leanh::lean_dec(v_i_809_);
                        v_i_809_ = v___x_817_;
                        state = 0;
                        continue;
                    } else {
                        v___x_819_ = lean_array_fget_borrowed(v_vals_808_, v_i_809_);
                        crate::leanh::lean_dec(v_i_809_);
                        crate::leanh::lean_inc(v___x_819_);
                        v___x_820_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_820_, 0, v___x_819_);
                        return v___x_820_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_821_: *mut crate::leanh::LeanObject,
    mut v_vals_822_: *mut crate::leanh::LeanObject,
    mut v_i_823_: *mut crate::leanh::LeanObject,
    mut v_k_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_821_, v_vals_822_, v_i_823_, v_k_824_);
    crate::leanh::lean_dec_ref(v_k_824_);
    crate::leanh::lean_dec_ref(v_vals_822_);
    crate::leanh::lean_dec_ref(v_keys_821_);
    return v_res_825_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_826_: usize = 0;
    let mut v___x_827_: usize = 0;
    let mut v___x_828_: usize = 0;
    v___x_826_ = 5usize;
    v___x_827_ = 1usize;
    v___x_828_ = lean_usize_shift_left(v___x_827_, v___x_826_);
    return v___x_828_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_829_: usize = 0;
    let mut v___x_830_: usize = 0;
    let mut v___x_831_: usize = 0;
    v___x_829_ = 1usize;
    v___x_830_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_831_ = lean_usize_sub(v___x_830_, v___x_829_);
    return v___x_831_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(
    mut v_x_832_: *mut crate::leanh::LeanObject,
    mut v_x_833_: usize,
    mut v_x_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: usize = 0;
    let mut v___x_838_: usize = 0;
    let mut v___x_839_: usize = 0;
    let mut v_j_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: usize = 0;
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_832_) == 0 {
                    v_es_835_ = crate::leanh::lean_ctor_get(v_x_832_, 0);
                    v___x_836_ = crate::leanh::lean_box(2);
                    v___x_837_ = 5usize;
                    v___x_838_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_839_ = lean_usize_land(v_x_833_, v___x_838_);
                    v_j_840_ = lean_usize_to_nat(v___x_839_);
                    v___x_841_ = lean_array_get_borrowed(v___x_836_, v_es_835_, v_j_840_);
                    crate::leanh::lean_dec(v_j_840_);
                    match crate::leanh::lean_obj_tag(v___x_841_) {
                        0 => {
                            v_key_842_ = crate::leanh::lean_ctor_get(v___x_841_, 0);
                            v_val_843_ = crate::leanh::lean_ctor_get(v___x_841_, 1);
                            v___x_844_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_834_, v_key_842_);
                            if v___x_844_ == 0 {
                                v___x_845_ = crate::leanh::lean_box(0);
                                return v___x_845_;
                            } else {
                                crate::leanh::lean_inc(v_val_843_);
                                v___x_846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_846_, 0, v_val_843_);
                                return v___x_846_;
                            }
                        }
                        1 => {
                            v_node_847_ = crate::leanh::lean_ctor_get(v___x_841_, 0);
                            v___x_848_ = lean_usize_shift_right(v_x_833_, v___x_837_);
                            v_x_832_ = v_node_847_;
                            v_x_833_ = v___x_848_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_850_ = crate::leanh::lean_box(0);
                            return v___x_850_;
                        }
                    }
                } else {
                    v_ks_851_ = crate::leanh::lean_ctor_get(v_x_832_, 0);
                    v_vs_852_ = crate::leanh::lean_ctor_get(v_x_832_, 1);
                    v___x_853_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_854_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_851_, v_vs_852_, v___x_853_, v_x_834_);
                    return v___x_854_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_855_: *mut crate::leanh::LeanObject,
    mut v_x_856_: *mut crate::leanh::LeanObject,
    mut v_x_857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4394__boxed_858_: usize = 0;
    let mut v_res_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4394__boxed_858_ = crate::leanh::lean_unbox_usize(v_x_856_);
    crate::leanh::lean_dec(v_x_856_);
    v_res_859_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_855_, v_x_4394__boxed_858_, v_x_857_);
    crate::leanh::lean_dec_ref(v_x_857_);
    crate::leanh::lean_dec_ref(v_x_855_);
    return v_res_859_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(
    mut v_x_860_: *mut crate::leanh::LeanObject,
    mut v_x_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_862_: u64 = 0;
    let mut v___x_863_: usize = 0;
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_862_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_861_);
    v___x_863_ = lean_uint64_to_usize(v___x_862_);
    v___x_864_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_860_, v___x_863_, v_x_861_);
    return v___x_864_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg___boxed(
    mut v_x_865_: *mut crate::leanh::LeanObject,
    mut v_x_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_867_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_x_865_, v_x_866_);
    crate::leanh::lean_dec_ref(v_x_866_);
    crate::leanh::lean_dec_ref(v_x_865_);
    return v_res_867_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_868_: *mut crate::leanh::LeanObject,
    mut v_x_869_: *mut crate::leanh::LeanObject,
    mut v_x_870_: *mut crate::leanh::LeanObject,
    mut v_x_871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_872_ = crate::leanh::lean_ctor_get(v_x_868_, 0);
                v_vs_873_ = crate::leanh::lean_ctor_get(v_x_868_, 1);
                v_isSharedCheck_897_ = (!crate::leanh::lean_is_exclusive(v_x_868_)) as u8;
                if v_isSharedCheck_897_ == 0 {
                    v___x_875_ = v_x_868_;
                    v_isShared_876_ = v_isSharedCheck_897_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_873_);
                    crate::leanh::lean_inc(v_ks_872_);
                    crate::leanh::lean_dec(v_x_868_);
                    v___x_875_ = crate::leanh::lean_box(0);
                    v_isShared_876_ = v_isSharedCheck_897_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_877_ = lean_array_get_size(v_ks_872_);
                v___x_878_ = lean_nat_dec_lt(v_x_869_, v___x_877_);
                if v___x_878_ == 0 {
                    crate::leanh::lean_dec(v_x_869_);
                    v___x_879_ = lean_array_push(v_ks_872_, v_x_870_);
                    v___x_880_ = lean_array_push(v_vs_873_, v_x_871_);
                    if v_isShared_876_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_875_, 1, v___x_880_);
                        crate::leanh::lean_ctor_set(v___x_875_, 0, v___x_879_);
                        v___x_882_ = v___x_875_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_883_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_879_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_880_);
                        v___x_882_ = v_reuseFailAlloc_883_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_884_ = lean_array_fget_borrowed(v_ks_872_, v_x_869_);
                    v___x_885_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_870_,
                            v_k_x27_884_,
                        );
                    if v___x_885_ == 0 {
                        if v_isShared_876_ == 0 {
                            v___x_887_ = v___x_875_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_891_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 0, v_ks_872_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 1, v_vs_873_);
                            v___x_887_ = v_reuseFailAlloc_891_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_892_ = lean_array_fset(v_ks_872_, v_x_869_, v_x_870_);
                        v___x_893_ = lean_array_fset(v_vs_873_, v_x_869_, v_x_871_);
                        crate::leanh::lean_dec(v_x_869_);
                        if v_isShared_876_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_875_, 1, v___x_893_);
                            crate::leanh::lean_ctor_set(v___x_875_, 0, v___x_892_);
                            v___x_895_ = v___x_875_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_896_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_892_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_893_);
                            v___x_895_ = v_reuseFailAlloc_896_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_882_;
            }
            3 => {
                v___x_888_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_889_ = lean_nat_add(v_x_869_, v___x_888_);
                crate::leanh::lean_dec(v_x_869_);
                v_x_868_ = v___x_887_;
                v_x_869_ = v___x_889_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_n_898_: *mut crate::leanh::LeanObject,
    mut v_k_899_: *mut crate::leanh::LeanObject,
    mut v_v_900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_901_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_902_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_898_, v___x_901_, v_k_899_, v_v_900_);
    return v___x_902_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_903_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(
    mut v_x_904_: *mut crate::leanh::LeanObject,
    mut v_x_905_: usize,
    mut v_x_906_: usize,
    mut v_x_907_: *mut crate::leanh::LeanObject,
    mut v_x_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: usize = 0;
    let mut v___x_911_: usize = 0;
    let mut v___x_912_: usize = 0;
    let mut v___x_913_: usize = 0;
    let mut v_j_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: u8 = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v_v_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v___x_934_: u8 = 0;
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut v_node_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_944_: u8 = 0;
    let mut v___x_945_: usize = 0;
    let mut v___x_946_: usize = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_953_: u8 = 0;
    let mut v_unused_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_964_: u8 = 0;
    let mut v_ks_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: usize = 0;
    let mut v___x_971_: u8 = 0;
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut v_reuseFailAlloc_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_904_) == 0 {
                    v_es_909_ = crate::leanh::lean_ctor_get(v_x_904_, 0);
                    v___x_910_ = 5usize;
                    v___x_911_ = 1usize;
                    v___x_912_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_913_ = lean_usize_land(v_x_905_, v___x_912_);
                    v_j_914_ = lean_usize_to_nat(v___x_913_);
                    v___x_915_ = lean_array_get_size(v_es_909_);
                    v___x_916_ = lean_nat_dec_lt(v_j_914_, v___x_915_);
                    if v___x_916_ == 0 {
                        crate::leanh::lean_dec(v_j_914_);
                        crate::leanh::lean_dec(v_x_908_);
                        crate::leanh::lean_dec_ref(v_x_907_);
                        return v_x_904_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_909_);
                        v_isSharedCheck_953_ = (!crate::leanh::lean_is_exclusive(v_x_904_)) as u8;
                        if v_isSharedCheck_953_ == 0 {
                            v_unused_954_ = crate::leanh::lean_ctor_get(v_x_904_, 0);
                            crate::leanh::lean_dec(v_unused_954_);
                            v___x_918_ = v_x_904_;
                            v_isShared_919_ = v_isSharedCheck_953_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_904_);
                            v___x_918_ = crate::leanh::lean_box(0);
                            v_isShared_919_ = v_isSharedCheck_953_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_955_ = crate::leanh::lean_ctor_get(v_x_904_, 0);
                    v_vs_956_ = crate::leanh::lean_ctor_get(v_x_904_, 1);
                    v_isSharedCheck_976_ = (!crate::leanh::lean_is_exclusive(v_x_904_)) as u8;
                    if v_isSharedCheck_976_ == 0 {
                        v___x_958_ = v_x_904_;
                        v_isShared_959_ = v_isSharedCheck_976_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_956_);
                        crate::leanh::lean_inc(v_ks_955_);
                        crate::leanh::lean_dec(v_x_904_);
                        v___x_958_ = crate::leanh::lean_box(0);
                        v_isShared_959_ = v_isSharedCheck_976_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_920_ = lean_array_fget(v_es_909_, v_j_914_);
                v___x_921_ = crate::leanh::lean_box(0);
                v_xs_x27_922_ = lean_array_fset(v_es_909_, v_j_914_, v___x_921_);
                match crate::leanh::lean_obj_tag(v_v_920_) {
                    0 => {
                        v_key_929_ = crate::leanh::lean_ctor_get(v_v_920_, 0);
                        v_val_930_ = crate::leanh::lean_ctor_get(v_v_920_, 1);
                        v_isSharedCheck_940_ = (!crate::leanh::lean_is_exclusive(v_v_920_)) as u8;
                        if v_isSharedCheck_940_ == 0 {
                            v___x_932_ = v_v_920_;
                            v_isShared_933_ = v_isSharedCheck_940_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_930_);
                            crate::leanh::lean_inc(v_key_929_);
                            crate::leanh::lean_dec(v_v_920_);
                            v___x_932_ = crate::leanh::lean_box(0);
                            v_isShared_933_ = v_isSharedCheck_940_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_941_ = crate::leanh::lean_ctor_get(v_v_920_, 0);
                        v_isSharedCheck_951_ = (!crate::leanh::lean_is_exclusive(v_v_920_)) as u8;
                        if v_isSharedCheck_951_ == 0 {
                            v___x_943_ = v_v_920_;
                            v_isShared_944_ = v_isSharedCheck_951_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_941_);
                            crate::leanh::lean_dec(v_v_920_);
                            v___x_943_ = crate::leanh::lean_box(0);
                            v_isShared_944_ = v_isSharedCheck_951_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_952_, 0, v_x_907_);
                        crate::leanh::lean_ctor_set(v___x_952_, 1, v_x_908_);
                        v___y_924_ = v___x_952_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_925_ = lean_array_fset(v_xs_x27_922_, v_j_914_, v___y_924_);
                crate::leanh::lean_dec(v_j_914_);
                if v_isShared_919_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_918_, 0, v___x_925_);
                    v___x_927_ = v___x_918_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
                    v___x_927_ = v_reuseFailAlloc_928_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_927_;
            }
            4 => {
                v___x_934_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_907_, v_key_929_,
                    );
                if v___x_934_ == 0 {
                    crate::leanh::lean_del_object(v___x_932_);
                    v___x_935_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_929_, v_val_930_, v_x_907_, v_x_908_,
                    );
                    v___x_936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_935_);
                    v___y_924_ = v___x_936_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_930_);
                    crate::leanh::lean_dec(v_key_929_);
                    if v_isShared_933_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_932_, 1, v_x_908_);
                        crate::leanh::lean_ctor_set(v___x_932_, 0, v_x_907_);
                        v___x_938_ = v___x_932_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_939_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_939_, 0, v_x_907_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_939_, 1, v_x_908_);
                        v___x_938_ = v_reuseFailAlloc_939_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_924_ = v___x_938_;
                state = 2;
                continue;
            }
            6 => {
                v___x_945_ = lean_usize_shift_right(v_x_905_, v___x_910_);
                v___x_946_ = lean_usize_add(v_x_906_, v___x_911_);
                v___x_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_node_941_, v___x_945_, v___x_946_, v_x_907_, v_x_908_);
                if v_isShared_944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_943_, 0, v___x_947_);
                    v___x_949_ = v___x_943_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
                    v___x_949_ = v_reuseFailAlloc_950_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_924_ = v___x_949_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_959_ == 0 {
                    v___x_961_ = v___x_958_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_975_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_975_, 0, v_ks_955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_975_, 1, v_vs_956_);
                    v___x_961_ = v_reuseFailAlloc_975_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_962_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v___x_961_, v_x_907_, v_x_908_);
                v___x_970_ = 7usize;
                v___x_971_ = lean_usize_dec_le(v___x_970_, v_x_906_);
                if v___x_971_ == 0 {
                    v___x_972_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_962_);
                    v___x_973_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
                    crate::leanh::lean_dec(v___x_972_);
                    v___y_964_ = v___x_974_;
                    state = 10;
                    continue;
                } else {
                    v___y_964_ = v___x_971_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_964_ == 0 {
                    v_ks_965_ = crate::leanh::lean_ctor_get(v_newNode_962_, 0);
                    crate::leanh::lean_inc_ref(v_ks_965_);
                    v_vs_966_ = crate::leanh::lean_ctor_get(v_newNode_962_, 1);
                    crate::leanh::lean_inc_ref(v_vs_966_);
                    crate::leanh::lean_dec_ref(v_newNode_962_);
                    v___x_967_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_968_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___closed__0);
                    v___x_969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_x_906_, v_ks_965_, v_vs_966_, v___x_967_, v___x_968_);
                    crate::leanh::lean_dec_ref(v_vs_966_);
                    crate::leanh::lean_dec_ref(v_ks_965_);
                    return v___x_969_;
                } else {
                    return v_newNode_962_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_depth_977_: usize,
    mut v_keys_978_: *mut crate::leanh::LeanObject,
    mut v_vals_979_: *mut crate::leanh::LeanObject,
    mut v_i_980_: *mut crate::leanh::LeanObject,
    mut v_entries_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: u8 = 0;
    let mut v_k_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u64 = 0;
    let mut v_h_987_: usize = 0;
    let mut v___x_988_: usize = 0;
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: usize = 0;
    let mut v___x_991_: usize = 0;
    let mut v___x_992_: usize = 0;
    let mut v_h_993_: usize = 0;
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_982_ = lean_array_get_size(v_keys_978_);
                v___x_983_ = lean_nat_dec_lt(v_i_980_, v___x_982_);
                if v___x_983_ == 0 {
                    crate::leanh::lean_dec(v_i_980_);
                    return v_entries_981_;
                } else {
                    v_k_984_ = lean_array_fget_borrowed(v_keys_978_, v_i_980_);
                    v_v_985_ = lean_array_fget_borrowed(v_vals_979_, v_i_980_);
                    v___x_986_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_984_);
                    v_h_987_ = lean_uint64_to_usize(v___x_986_);
                    v___x_988_ = 5usize;
                    v___x_989_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_990_ = 1usize;
                    v___x_991_ = lean_usize_sub(v_depth_977_, v___x_990_);
                    v___x_992_ = lean_usize_mul(v___x_988_, v___x_991_);
                    v_h_993_ = lean_usize_shift_right(v_h_987_, v___x_992_);
                    v___x_994_ = lean_nat_add(v_i_980_, v___x_989_);
                    crate::leanh::lean_dec(v_i_980_);
                    crate::leanh::lean_inc(v_v_985_);
                    crate::leanh::lean_inc(v_k_984_);
                    v___x_995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_entries_981_, v_h_993_, v_depth_977_, v_k_984_, v_v_985_);
                    v_i_980_ = v___x_994_;
                    v_entries_981_ = v___x_995_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_997_: *mut crate::leanh::LeanObject,
    mut v_keys_998_: *mut crate::leanh::LeanObject,
    mut v_vals_999_: *mut crate::leanh::LeanObject,
    mut v_i_1000_: *mut crate::leanh::LeanObject,
    mut v_entries_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1002_: usize = 0;
    let mut v_res_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1002_ = crate::leanh::lean_unbox_usize(v_depth_997_);
    crate::leanh::lean_dec(v_depth_997_);
    v_res_1003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1002_, v_keys_998_, v_vals_999_, v_i_1000_, v_entries_1001_);
    crate::leanh::lean_dec_ref(v_vals_999_);
    crate::leanh::lean_dec_ref(v_keys_998_);
    return v_res_1003_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_1004_: *mut crate::leanh::LeanObject,
    mut v_x_1005_: *mut crate::leanh::LeanObject,
    mut v_x_1006_: *mut crate::leanh::LeanObject,
    mut v_x_1007_: *mut crate::leanh::LeanObject,
    mut v_x_1008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4541__boxed_1009_: usize = 0;
    let mut v_x_4542__boxed_1010_: usize = 0;
    let mut v_res_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4541__boxed_1009_ = crate::leanh::lean_unbox_usize(v_x_1005_);
    crate::leanh::lean_dec(v_x_1005_);
    v_x_4542__boxed_1010_ = crate::leanh::lean_unbox_usize(v_x_1006_);
    crate::leanh::lean_dec(v_x_1006_);
    v_res_1011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_1004_, v_x_4541__boxed_1009_, v_x_4542__boxed_1010_, v_x_1007_, v_x_1008_);
    return v_res_1011_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(
    mut v_x_1012_: *mut crate::leanh::LeanObject,
    mut v_x_1013_: *mut crate::leanh::LeanObject,
    mut v_x_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1015_: u64 = 0;
    let mut v___x_1016_: usize = 0;
    let mut v___x_1017_: usize = 0;
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1013_);
    v___x_1016_ = lean_uint64_to_usize(v___x_1015_);
    v___x_1017_ = 1usize;
    v___x_1018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_1012_, v___x_1016_, v___x_1017_, v_x_1013_, v_x_1014_);
    return v___x_1018_;
}
pub unsafe fn l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(
    mut v_op_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
    mut v_a_1023_: *mut crate::leanh::LeanObject,
    mut v_a_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1032_: u8 = 0;
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1036_: u8 = 0;
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_counters_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchors_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut v_isSharedCheck_1065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1026_ = lean_st_ref_get(v_a_1020_);
                v_lawfulEqCmpMap_1027_ = crate::leanh::lean_ctor_get(v___x_1026_, 6);
                crate::leanh::lean_inc_ref(v_lawfulEqCmpMap_1027_);
                crate::leanh::lean_dec(v___x_1026_);
                v___x_1028_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_lawfulEqCmpMap_1027_, v_op_1019_);
                crate::leanh::lean_dec_ref(v_lawfulEqCmpMap_1027_);
                if crate::leanh::lean_obj_tag(v___x_1028_) == 1 {
                    crate::leanh::lean_dec_ref(v_op_1019_);
                    v_val_1029_ = crate::leanh::lean_ctor_get(v___x_1028_, 0);
                    v_isSharedCheck_1036_ = (!crate::leanh::lean_is_exclusive(v___x_1028_)) as u8;
                    if v_isSharedCheck_1036_ == 0 {
                        v___x_1031_ = v___x_1028_;
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1029_);
                        crate::leanh::lean_dec(v___x_1028_);
                        v___x_1031_ = crate::leanh::lean_box(0);
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1028_);
                    crate::leanh::lean_inc_ref(v_op_1019_);
                    v___x_1037_ = l___private_Lean_Meta_Tactic_Grind_LawfulEqCmp_0__Lean_Meta_Grind_getLawfulEqCmpThm_x3f_go_x3f(v_op_1019_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
                    if crate::leanh::lean_obj_tag(v___x_1037_) == 0 {
                        v_a_1038_ = crate::leanh::lean_ctor_get(v___x_1037_, 0);
                        v_isSharedCheck_1065_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1037_)) as u8;
                        if v_isSharedCheck_1065_ == 0 {
                            v___x_1040_ = v___x_1037_;
                            v_isShared_1041_ = v_isSharedCheck_1065_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1038_);
                            crate::leanh::lean_dec(v___x_1037_);
                            v___x_1040_ = crate::leanh::lean_box(0);
                            v_isShared_1041_ = v_isSharedCheck_1065_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_op_1019_);
                        return v___x_1037_;
                    }
                }
            }
            1 => {
                if v_isShared_1032_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1031_, 0);
                    v___x_1034_ = v___x_1031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_val_1029_);
                    v___x_1034_ = v_reuseFailAlloc_1035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1034_;
            }
            3 => {
                v___x_1042_ = lean_st_ref_take(v_a_1020_);
                v_congrThms_1043_ = crate::leanh::lean_ctor_get(v___x_1042_, 0);
                v_simp_1044_ = crate::leanh::lean_ctor_get(v___x_1042_, 1);
                v_lastTag_1045_ = crate::leanh::lean_ctor_get(v___x_1042_, 2);
                v_counters_1046_ = crate::leanh::lean_ctor_get(v___x_1042_, 3);
                v_splitDiags_1047_ = crate::leanh::lean_ctor_get(v___x_1042_, 4);
                v_ematchDiags_1048_ = crate::leanh::lean_ctor_get(v___x_1042_, 5);
                v_lawfulEqCmpMap_1049_ = crate::leanh::lean_ctor_get(v___x_1042_, 6);
                v_reflCmpMap_1050_ = crate::leanh::lean_ctor_get(v___x_1042_, 7);
                v_anchors_1051_ = crate::leanh::lean_ctor_get(v___x_1042_, 8);
                v_instanceMap_1052_ = crate::leanh::lean_ctor_get(v___x_1042_, 9);
                v_isSharedCheck_1064_ = (!crate::leanh::lean_is_exclusive(v___x_1042_)) as u8;
                if v_isSharedCheck_1064_ == 0 {
                    v___x_1054_ = v___x_1042_;
                    v_isShared_1055_ = v_isSharedCheck_1064_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_instanceMap_1052_);
                    crate::leanh::lean_inc(v_anchors_1051_);
                    crate::leanh::lean_inc(v_reflCmpMap_1050_);
                    crate::leanh::lean_inc(v_lawfulEqCmpMap_1049_);
                    crate::leanh::lean_inc(v_ematchDiags_1048_);
                    crate::leanh::lean_inc(v_splitDiags_1047_);
                    crate::leanh::lean_inc(v_counters_1046_);
                    crate::leanh::lean_inc(v_lastTag_1045_);
                    crate::leanh::lean_inc(v_simp_1044_);
                    crate::leanh::lean_inc(v_congrThms_1043_);
                    crate::leanh::lean_dec(v___x_1042_);
                    v___x_1054_ = crate::leanh::lean_box(0);
                    v_isShared_1055_ = v_isSharedCheck_1064_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_1038_);
                v___x_1056_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(v_lawfulEqCmpMap_1049_, v_op_1019_, v_a_1038_);
                if v_isShared_1055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1054_, 6, v___x_1056_);
                    v___x_1058_ = v___x_1054_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_congrThms_1043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_simp_1044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_lastTag_1045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_counters_1046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 4, v_splitDiags_1047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 5, v_ematchDiags_1048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 6, v___x_1056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 7, v_reflCmpMap_1050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 8, v_anchors_1051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 9, v_instanceMap_1052_);
                    v___x_1058_ = v_reuseFailAlloc_1063_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1059_ = lean_st_ref_set(v_a_1020_, v___x_1058_);
                if v_isShared_1041_ == 0 {
                    v___x_1061_ = v___x_1040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1038_);
                    v___x_1061_ = v_reuseFailAlloc_1062_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg___boxed(
    mut v_op_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v_a_1069_: *mut crate::leanh::LeanObject,
    mut v_a_1070_: *mut crate::leanh::LeanObject,
    mut v_a_1071_: *mut crate::leanh::LeanObject,
    mut v_a_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(
        v_op_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_,
    );
    crate::leanh::lean_dec(v_a_1071_);
    crate::leanh::lean_dec_ref(v_a_1070_);
    crate::leanh::lean_dec(v_a_1069_);
    crate::leanh::lean_dec_ref(v_a_1068_);
    crate::leanh::lean_dec(v_a_1067_);
    return v_res_1073_;
}
pub unsafe fn l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f(
    mut v_op_1074_: *mut crate::leanh::LeanObject,
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_a_1078_: *mut crate::leanh::LeanObject,
    mut v_a_1079_: *mut crate::leanh::LeanObject,
    mut v_a_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(
        v_op_1074_, v_a_1077_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_,
    );
    return v___x_1085_;
}
pub unsafe fn l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___boxed(
    mut v_op_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_a_1094_: *mut crate::leanh::LeanObject,
    mut v_a_1095_: *mut crate::leanh::LeanObject,
    mut v_a_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1097_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f(
        v_op_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_,
        v_a_1094_, v_a_1095_,
    );
    crate::leanh::lean_dec(v_a_1095_);
    crate::leanh::lean_dec_ref(v_a_1094_);
    crate::leanh::lean_dec(v_a_1093_);
    crate::leanh::lean_dec_ref(v_a_1092_);
    crate::leanh::lean_dec(v_a_1091_);
    crate::leanh::lean_dec_ref(v_a_1090_);
    crate::leanh::lean_dec(v_a_1089_);
    crate::leanh::lean_dec_ref(v_a_1088_);
    crate::leanh::lean_dec(v_a_1087_);
    return v_res_1097_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0(
    mut v_00_u03b2_1098_: *mut crate::leanh::LeanObject,
    mut v_x_1099_: *mut crate::leanh::LeanObject,
    mut v_x_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___redArg(v_x_1099_, v_x_1100_);
    return v___x_1101_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0___boxed(
    mut v_00_u03b2_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: *mut crate::leanh::LeanObject,
    mut v_x_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1105_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0(
            v_00_u03b2_1102_,
            v_x_1103_,
            v_x_1104_,
        );
    crate::leanh::lean_dec_ref(v_x_1104_);
    crate::leanh::lean_dec_ref(v_x_1103_);
    return v_res_1105_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1(
    mut v_00_u03b2_1106_: *mut crate::leanh::LeanObject,
    mut v_x_1107_: *mut crate::leanh::LeanObject,
    mut v_x_1108_: *mut crate::leanh::LeanObject,
    mut v_x_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1___redArg(v_x_1107_, v_x_1108_, v_x_1109_);
    return v___x_1110_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0(
    mut v_00_u03b2_1111_: *mut crate::leanh::LeanObject,
    mut v_x_1112_: *mut crate::leanh::LeanObject,
    mut v_x_1113_: usize,
    mut v_x_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1115_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___redArg(v_x_1112_, v_x_1113_, v_x_1114_);
    return v___x_1115_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1116_: *mut crate::leanh::LeanObject,
    mut v_x_1117_: *mut crate::leanh::LeanObject,
    mut v_x_1118_: *mut crate::leanh::LeanObject,
    mut v_x_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4794__boxed_1120_: usize = 0;
    let mut v_res_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4794__boxed_1120_ = crate::leanh::lean_unbox_usize(v_x_1118_);
    crate::leanh::lean_dec(v_x_1118_);
    v_res_1121_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0(v_00_u03b2_1116_, v_x_1117_, v_x_4794__boxed_1120_, v_x_1119_);
    crate::leanh::lean_dec_ref(v_x_1119_);
    crate::leanh::lean_dec_ref(v_x_1117_);
    return v_res_1121_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2(
    mut v_00_u03b2_1122_: *mut crate::leanh::LeanObject,
    mut v_x_1123_: *mut crate::leanh::LeanObject,
    mut v_x_1124_: usize,
    mut v_x_1125_: usize,
    mut v_x_1126_: *mut crate::leanh::LeanObject,
    mut v_x_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___redArg(v_x_1123_, v_x_1124_, v_x_1125_, v_x_1126_, v_x_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_1129_: *mut crate::leanh::LeanObject,
    mut v_x_1130_: *mut crate::leanh::LeanObject,
    mut v_x_1131_: *mut crate::leanh::LeanObject,
    mut v_x_1132_: *mut crate::leanh::LeanObject,
    mut v_x_1133_: *mut crate::leanh::LeanObject,
    mut v_x_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4805__boxed_1135_: usize = 0;
    let mut v_x_4806__boxed_1136_: usize = 0;
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4805__boxed_1135_ = crate::leanh::lean_unbox_usize(v_x_1131_);
    crate::leanh::lean_dec(v_x_1131_);
    v_x_4806__boxed_1136_ = crate::leanh::lean_unbox_usize(v_x_1132_);
    crate::leanh::lean_dec(v_x_1132_);
    v_res_1137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2(v_00_u03b2_1129_, v_x_1130_, v_x_4805__boxed_1135_, v_x_4806__boxed_1136_, v_x_1133_, v_x_1134_);
    return v_res_1137_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1138_: *mut crate::leanh::LeanObject,
    mut v_keys_1139_: *mut crate::leanh::LeanObject,
    mut v_vals_1140_: *mut crate::leanh::LeanObject,
    mut v_heq_1141_: *mut crate::leanh::LeanObject,
    mut v_i_1142_: *mut crate::leanh::LeanObject,
    mut v_k_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1139_, v_vals_1140_, v_i_1142_, v_k_1143_);
    return v___x_1144_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1145_: *mut crate::leanh::LeanObject,
    mut v_keys_1146_: *mut crate::leanh::LeanObject,
    mut v_vals_1147_: *mut crate::leanh::LeanObject,
    mut v_heq_1148_: *mut crate::leanh::LeanObject,
    mut v_i_1149_: *mut crate::leanh::LeanObject,
    mut v_k_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1151_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1145_, v_keys_1146_, v_vals_1147_, v_heq_1148_, v_i_1149_, v_k_1150_);
    crate::leanh::lean_dec_ref(v_k_1150_);
    crate::leanh::lean_dec_ref(v_vals_1147_);
    crate::leanh::lean_dec_ref(v_keys_1146_);
    return v_res_1151_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1152_: *mut crate::leanh::LeanObject,
    mut v_n_1153_: *mut crate::leanh::LeanObject,
    mut v_k_1154_: *mut crate::leanh::LeanObject,
    mut v_v_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v_n_1153_, v_k_1154_, v_v_1155_);
    return v___x_1156_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1157_: *mut crate::leanh::LeanObject,
    mut v_depth_1158_: usize,
    mut v_keys_1159_: *mut crate::leanh::LeanObject,
    mut v_vals_1160_: *mut crate::leanh::LeanObject,
    mut v_heq_1161_: *mut crate::leanh::LeanObject,
    mut v_i_1162_: *mut crate::leanh::LeanObject,
    mut v_entries_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1158_, v_keys_1159_, v_vals_1160_, v_i_1162_, v_entries_1163_);
    return v___x_1164_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_1165_: *mut crate::leanh::LeanObject,
    mut v_depth_1166_: *mut crate::leanh::LeanObject,
    mut v_keys_1167_: *mut crate::leanh::LeanObject,
    mut v_vals_1168_: *mut crate::leanh::LeanObject,
    mut v_heq_1169_: *mut crate::leanh::LeanObject,
    mut v_i_1170_: *mut crate::leanh::LeanObject,
    mut v_entries_1171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1172_: usize = 0;
    let mut v_res_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1172_ = crate::leanh::lean_unbox_usize(v_depth_1166_);
    crate::leanh::lean_dec(v_depth_1166_);
    v_res_1173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1165_, v_depth_boxed_1172_, v_keys_1167_, v_vals_1168_, v_heq_1169_, v_i_1170_, v_entries_1171_);
    crate::leanh::lean_dec_ref(v_vals_1168_);
    crate::leanh::lean_dec_ref(v_keys_1167_);
    return v_res_1173_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1174_: *mut crate::leanh::LeanObject,
    mut v_x_1175_: *mut crate::leanh::LeanObject,
    mut v_x_1176_: *mut crate::leanh::LeanObject,
    mut v_x_1177_: *mut crate::leanh::LeanObject,
    mut v_x_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getLawfulEqCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1175_, v_x_1176_, v_x_1177_, v_x_1178_);
    return v___x_1179_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateLawfulEqCmp(
    mut v_e_1180_: *mut crate::leanh::LeanObject,
    mut v_a_1181_: *mut crate::leanh::LeanObject,
    mut v_a_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v_val_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1206_: u8 = 0;
    let mut v___x_1207_: u8 = 0;
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1223_: u8 = 0;
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1227_: u8 = 0;
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut v_a_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1232_: u8 = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1236_: u8 = 0;
    let mut v_a_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1249_: u8 = 0;
    let mut v_a_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1257_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1192_ = l_Lean_Meta_Grind_getBinOp(v_e_1180_);
                if crate::leanh::lean_obj_tag(v___x_1192_) == 1 {
                    v_val_1193_ = crate::leanh::lean_ctor_get(v___x_1192_, 0);
                    crate::leanh::lean_inc(v_val_1193_);
                    crate::leanh::lean_dec_ref_known(v___x_1192_, 1);
                    v___x_1194_ = l_Lean_Meta_Grind_getLawfulEqCmpThm_x3f___redArg(
                        v_val_1193_,
                        v_a_1184_,
                        v_a_1187_,
                        v_a_1188_,
                        v_a_1189_,
                        v_a_1190_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1194_) == 0 {
                        v_a_1195_ = crate::leanh::lean_ctor_get(v___x_1194_, 0);
                        v_isSharedCheck_1249_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1194_)) as u8;
                        if v_isSharedCheck_1249_ == 0 {
                            v___x_1197_ = v___x_1194_;
                            v_isShared_1198_ = v_isSharedCheck_1249_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1195_);
                            crate::leanh::lean_dec(v___x_1194_);
                            v___x_1197_ = crate::leanh::lean_box(0);
                            v_isShared_1198_ = v_isSharedCheck_1249_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_1180_);
                        v_a_1250_ = crate::leanh::lean_ctor_get(v___x_1194_, 0);
                        v_isSharedCheck_1257_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1194_)) as u8;
                        if v_isSharedCheck_1257_ == 0 {
                            v___x_1252_ = v___x_1194_;
                            v_isShared_1253_ = v_isSharedCheck_1257_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1250_);
                            crate::leanh::lean_dec(v___x_1194_);
                            v___x_1252_ = crate::leanh::lean_box(0);
                            v_isShared_1253_ = v_isSharedCheck_1257_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1192_);
                    crate::leanh::lean_dec_ref(v_e_1180_);
                    v___x_1258_ = crate::leanh::lean_box(0);
                    v___x_1259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1259_, 0, v___x_1258_);
                    return v___x_1259_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1195_) == 1 {
                    crate::leanh::lean_del_object(v___x_1197_);
                    v_val_1199_ = crate::leanh::lean_ctor_get(v_a_1195_, 0);
                    crate::leanh::lean_inc(v_val_1199_);
                    crate::leanh::lean_dec_ref_known(v_a_1195_, 1);
                    v___x_1200_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_1185_);
                    if crate::leanh::lean_obj_tag(v___x_1200_) == 0 {
                        v_a_1201_ = crate::leanh::lean_ctor_get(v___x_1200_, 0);
                        crate::leanh::lean_inc(v_a_1201_);
                        crate::leanh::lean_dec_ref_known(v___x_1200_, 1);
                        v___x_1202_ =
                            l_Lean_Meta_Grind_isEqv___redArg(v_e_1180_, v_a_1201_, v_a_1181_);
                        if crate::leanh::lean_obj_tag(v___x_1202_) == 0 {
                            v_a_1203_ = crate::leanh::lean_ctor_get(v___x_1202_, 0);
                            v_isSharedCheck_1228_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1202_)) as u8;
                            if v_isSharedCheck_1228_ == 0 {
                                v___x_1205_ = v___x_1202_;
                                v_isShared_1206_ = v_isSharedCheck_1228_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1203_);
                                crate::leanh::lean_dec(v___x_1202_);
                                v___x_1205_ = crate::leanh::lean_box(0);
                                v_isShared_1206_ = v_isSharedCheck_1228_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1201_);
                            crate::leanh::lean_dec(v_val_1199_);
                            crate::leanh::lean_dec_ref(v_e_1180_);
                            v_a_1229_ = crate::leanh::lean_ctor_get(v___x_1202_, 0);
                            v_isSharedCheck_1236_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1202_)) as u8;
                            if v_isSharedCheck_1236_ == 0 {
                                v___x_1231_ = v___x_1202_;
                                v_isShared_1232_ = v_isSharedCheck_1236_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1229_);
                                crate::leanh::lean_dec(v___x_1202_);
                                v___x_1231_ = crate::leanh::lean_box(0);
                                v_isShared_1232_ = v_isSharedCheck_1236_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1199_);
                        crate::leanh::lean_dec_ref(v_e_1180_);
                        v_a_1237_ = crate::leanh::lean_ctor_get(v___x_1200_, 0);
                        v_isSharedCheck_1244_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1200_)) as u8;
                        if v_isSharedCheck_1244_ == 0 {
                            v___x_1239_ = v___x_1200_;
                            v_isShared_1240_ = v_isSharedCheck_1244_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1237_);
                            crate::leanh::lean_dec(v___x_1200_);
                            v___x_1239_ = crate::leanh::lean_box(0);
                            v_isShared_1240_ = v_isSharedCheck_1244_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1195_);
                    crate::leanh::lean_dec_ref(v_e_1180_);
                    v___x_1245_ = crate::leanh::lean_box(0);
                    if v_isShared_1198_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1245_);
                        v___x_1247_ = v___x_1197_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
                        v___x_1247_ = v_reuseFailAlloc_1248_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1207_ = (crate::leanh::lean_unbox(v_a_1203_) as u8);
                crate::leanh::lean_dec(v_a_1203_);
                if v___x_1207_ == 0 {
                    crate::leanh::lean_dec(v_a_1201_);
                    crate::leanh::lean_dec(v_val_1199_);
                    crate::leanh::lean_dec_ref(v_e_1180_);
                    v___x_1208_ = crate::leanh::lean_box(0);
                    if v_isShared_1206_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1205_, 0, v___x_1208_);
                        v___x_1210_ = v___x_1205_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
                        v___x_1210_ = v_reuseFailAlloc_1211_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1205_);
                    v___x_1212_ = l_Lean_Expr_appFn_x21(v_e_1180_);
                    v___x_1213_ = l_Lean_Expr_appArg_x21(v_e_1180_);
                    crate::leanh::lean_inc(v_a_1190_);
                    crate::leanh::lean_inc_ref(v_a_1189_);
                    crate::leanh::lean_inc(v_a_1188_);
                    crate::leanh::lean_inc_ref(v_a_1187_);
                    crate::leanh::lean_inc(v_a_1186_);
                    crate::leanh::lean_inc_ref(v_a_1185_);
                    crate::leanh::lean_inc(v_a_1184_);
                    crate::leanh::lean_inc_ref(v_a_1183_);
                    crate::leanh::lean_inc(v_a_1182_);
                    crate::leanh::lean_inc(v_a_1181_);
                    v___x_1214_ = lean_grind_mk_eq_proof(
                        v_e_1180_, v_a_1201_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_,
                        v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1214_) == 0 {
                        v_a_1215_ = crate::leanh::lean_ctor_get(v___x_1214_, 0);
                        crate::leanh::lean_inc(v_a_1215_);
                        crate::leanh::lean_dec_ref_known(v___x_1214_, 1);
                        v___x_1216_ = l_Lean_Expr_appArg_x21(v___x_1212_);
                        crate::leanh::lean_dec_ref(v___x_1212_);
                        crate::leanh::lean_inc_ref(v___x_1213_);
                        crate::leanh::lean_inc_ref(v___x_1216_);
                        v___x_1217_ =
                            l_Lean_mkApp3(v_val_1199_, v___x_1216_, v___x_1213_, v_a_1215_);
                        v___x_1218_ = 0;
                        v___x_1219_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                            v___x_1216_,
                            v___x_1213_,
                            v___x_1217_,
                            v___x_1218_,
                            v_a_1181_,
                            v_a_1183_,
                            v_a_1187_,
                            v_a_1188_,
                            v_a_1189_,
                            v_a_1190_,
                        );
                        return v___x_1219_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1213_);
                        crate::leanh::lean_dec_ref(v___x_1212_);
                        crate::leanh::lean_dec(v_val_1199_);
                        v_a_1220_ = crate::leanh::lean_ctor_get(v___x_1214_, 0);
                        v_isSharedCheck_1227_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1214_)) as u8;
                        if v_isSharedCheck_1227_ == 0 {
                            v___x_1222_ = v___x_1214_;
                            v_isShared_1223_ = v_isSharedCheck_1227_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1220_);
                            crate::leanh::lean_dec(v___x_1214_);
                            v___x_1222_ = crate::leanh::lean_box(0);
                            v_isShared_1223_ = v_isSharedCheck_1227_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1210_;
            }
            4 => {
                if v_isShared_1223_ == 0 {
                    v___x_1225_ = v___x_1222_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
                    v___x_1225_ = v_reuseFailAlloc_1226_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1225_;
            }
            6 => {
                if v_isShared_1232_ == 0 {
                    v___x_1234_ = v___x_1231_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
                    v___x_1234_ = v_reuseFailAlloc_1235_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1234_;
            }
            8 => {
                if v_isShared_1240_ == 0 {
                    v___x_1242_ = v___x_1239_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
                    v___x_1242_ = v_reuseFailAlloc_1243_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1242_;
            }
            10 => {
                return v___x_1247_;
            }
            11 => {
                if v_isShared_1253_ == 0 {
                    v___x_1255_ = v___x_1252_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
                    v___x_1255_ = v_reuseFailAlloc_1256_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateLawfulEqCmp___boxed(
    mut v_e_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
    mut v_a_1266_: *mut crate::leanh::LeanObject,
    mut v_a_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1272_ = l_Lean_Meta_Grind_propagateLawfulEqCmp(
        v_e_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_,
        v_a_1268_, v_a_1269_, v_a_1270_,
    );
    crate::leanh::lean_dec(v_a_1270_);
    crate::leanh::lean_dec_ref(v_a_1269_);
    crate::leanh::lean_dec(v_a_1268_);
    crate::leanh::lean_dec_ref(v_a_1267_);
    crate::leanh::lean_dec(v_a_1266_);
    crate::leanh::lean_dec_ref(v_a_1265_);
    crate::leanh::lean_dec(v_a_1264_);
    crate::leanh::lean_dec_ref(v_a_1263_);
    crate::leanh::lean_dec(v_a_1262_);
    crate::leanh::lean_dec(v_a_1261_);
    return v_res_1272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
}
