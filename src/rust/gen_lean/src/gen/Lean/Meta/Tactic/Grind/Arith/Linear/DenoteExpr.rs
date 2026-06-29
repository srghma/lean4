// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
// Imports: Lean.Meta.Tactic.Grind.Arith.Util Lean.Meta.Tactic.Grind.Arith.Linear.Util Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
use crate::ffi::{
    lean_grind_internalize, lean_int_dec_eq, lean_int_dec_lt, lean_nat_abs, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_to_int, lean_st_ref_get,
};
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Nat_mkType, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkIntLit, l_Lean_mkNatLit, l_Lean_mkNot,
    l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_Level_succ___override};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Functions::l_Lean_Meta_Grind_Arith_CommRing_checkInst;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
    l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg,
    l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg, l_Lean_Meta_Grind_Arith_Linear_getOne,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util,
    l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_preprocessLight___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 102, 105, 110, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__0_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__5_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__5_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__6_value) as *mut crate::leanh::LeanObject,18388652353510661091 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__0_value) as *mut crate::leanh::LeanObject,12847922472053947547 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__8_value) as *mut crate::leanh::LeanObject,10422657989269798688 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__0_value) as *mut crate::leanh::LeanObject,18134279130838690737 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__5_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__2_value) as *mut crate::leanh::LeanObject,7102027102192867304 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__6_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject,10040236838748678500 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__5_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__5_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,9341924117480681831 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_CommRing_Poly_toIntModuleExpr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Poly_toIntModuleExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__0(
    mut v_toApplicative_1690_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1691_: *mut crate::leanh::LeanObject,
    mut v_k_1692_: *mut crate::leanh::LeanObject,
    mut v_x_1693_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_1695_ = crate::leanh::lean_ctor_get(v_____do__lift_1694_, 30);
                v_toPure_1696_ = crate::leanh::lean_ctor_get(v_toApplicative_1690_, 1);
                crate::leanh::lean_inc(v_toPure_1696_);
                crate::leanh::lean_dec_ref(v_toApplicative_1690_);
                v_zsmulFn_1697_ = crate::leanh::lean_ctor_get(v_____do__lift_1691_, 23);
                crate::leanh::lean_inc_ref(v_zsmulFn_1697_);
                crate::leanh::lean_dec_ref(v_____do__lift_1691_);
                v_size_1698_ = crate::leanh::lean_ctor_get(v_vars_1695_, 2);
                v___x_1699_ = l_Lean_mkIntLit(v_k_1692_);
                v___x_1704_ = l_Lean_instInhabitedExpr;
                v___x_1705_ = lean_nat_dec_lt(v_x_1693_, v_size_1698_);
                if v___x_1705_ == 0 {
                    v___x_1706_ = l_outOfBounds___redArg(v___x_1704_);
                    v___y_1701_ = v___x_1706_;
                    state = 1;
                    continue;
                } else {
                    v___x_1707_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1704_,
                        v_vars_1695_,
                        v_x_1693_,
                    );
                    v___y_1701_ = v___x_1707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = l_Lean_mkAppB(v_zsmulFn_1697_, v___x_1699_, v___y_1701_);
                v___x_1703_ = crate::leanh::lean_apply_2(
                    v_toPure_1696_,
                    crate::leanh::lean_box(0),
                    v___x_1702_,
                );
                return v___x_1703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__0___boxed(
    mut v_toApplicative_1708_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1709_: *mut crate::leanh::LeanObject,
    mut v_k_1710_: *mut crate::leanh::LeanObject,
    mut v_x_1711_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1713_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__0(v_toApplicative_1708_, v_____do__lift_1709_, v_k_1710_, v_x_1711_, v_____do__lift_1712_);
    crate::leanh::lean_dec_ref(v_____do__lift_1712_);
    crate::leanh::lean_dec(v_x_1711_);
    crate::leanh::lean_dec(v_k_1710_);
    return v_res_1713_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__1(
    mut v_toApplicative_1714_: *mut crate::leanh::LeanObject,
    mut v_k_1715_: *mut crate::leanh::LeanObject,
    mut v_x_1716_: *mut crate::leanh::LeanObject,
    mut v_toBind_1717_: *mut crate::leanh::LeanObject,
    mut v_inst_1718_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1720_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___f_1720_, 0, v_toApplicative_1714_);
    crate::leanh::lean_closure_set(v___f_1720_, 1, v_____do__lift_1719_);
    crate::leanh::lean_closure_set(v___f_1720_, 2, v_k_1715_);
    crate::leanh::lean_closure_set(v___f_1720_, 3, v_x_1716_);
    v___x_1721_ = crate::leanh::lean_apply_4(
        v_toBind_1717_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1718_,
        v___f_1720_,
    );
    return v___x_1721_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__2(
    mut v_toApplicative_1722_: *mut crate::leanh::LeanObject,
    mut v_x_1723_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    v_vars_1725_ = crate::leanh::lean_ctor_get(v_____do__lift_1724_, 30);
    v_toPure_1726_ = crate::leanh::lean_ctor_get(v_toApplicative_1722_, 1);
    crate::leanh::lean_inc(v_toPure_1726_);
    crate::leanh::lean_dec_ref(v_toApplicative_1722_);
    v_size_1727_ = crate::leanh::lean_ctor_get(v_vars_1725_, 2);
    v___x_1728_ = l_Lean_instInhabitedExpr;
    v___x_1729_ = lean_nat_dec_lt(v_x_1723_, v_size_1727_);
    if v___x_1729_ == 0 {
        let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1730_ = l_outOfBounds___redArg(v___x_1728_);
        v___x_1731_ =
            crate::leanh::lean_apply_2(v_toPure_1726_, crate::leanh::lean_box(0), v___x_1730_);
        return v___x_1731_;
    } else {
        let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1732_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1728_, v_vars_1725_, v_x_1723_);
        v___x_1733_ =
            crate::leanh::lean_apply_2(v_toPure_1726_, crate::leanh::lean_box(0), v___x_1732_);
        return v___x_1733_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__2___boxed(
    mut v_toApplicative_1734_: *mut crate::leanh::LeanObject,
    mut v_x_1735_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1737_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__2(v_toApplicative_1734_, v_x_1735_, v_____do__lift_1736_);
    crate::leanh::lean_dec_ref(v_____do__lift_1736_);
    crate::leanh::lean_dec(v_x_1735_);
    return v_res_1737_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1739_ = lean_nat_to_int(v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg(
    mut v_inst_1740_: *mut crate::leanh::LeanObject,
    mut v_inst_1741_: *mut crate::leanh::LeanObject,
    mut v_k_1742_: *mut crate::leanh::LeanObject,
    mut v_x_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: u8 = 0;
    v___x_1744_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0);
    v___x_1745_ = lean_int_dec_eq(v_k_1742_, v___x_1744_);
    if v___x_1745_ == 0 {
        let mut v_toApplicative_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1746_ = crate::leanh::lean_ctor_get(v_inst_1740_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1746_);
        v_toBind_1747_ = crate::leanh::lean_ctor_get(v_inst_1740_, 1);
        crate::leanh::lean_inc_n(v_toBind_1747_, 2);
        crate::leanh::lean_dec_ref(v_inst_1740_);
        crate::leanh::lean_inc(v_inst_1741_);
        v___f_1748_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__1 as *mut core::ffi::c_void, 6, 5);
        crate::leanh::lean_closure_set(v___f_1748_, 0, v_toApplicative_1746_);
        crate::leanh::lean_closure_set(v___f_1748_, 1, v_k_1742_);
        crate::leanh::lean_closure_set(v___f_1748_, 2, v_x_1743_);
        crate::leanh::lean_closure_set(v___f_1748_, 3, v_toBind_1747_);
        crate::leanh::lean_closure_set(v___f_1748_, 4, v_inst_1741_);
        v___x_1749_ = crate::leanh::lean_apply_4(
            v_toBind_1747_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_1741_,
            v___f_1748_,
        );
        return v___x_1749_;
    } else {
        let mut v_toApplicative_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_1742_);
        v_toApplicative_1750_ = crate::leanh::lean_ctor_get(v_inst_1740_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1750_);
        v_toBind_1751_ = crate::leanh::lean_ctor_get(v_inst_1740_, 1);
        crate::leanh::lean_inc(v_toBind_1751_);
        crate::leanh::lean_dec_ref(v_inst_1740_);
        v___f_1752_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v___f_1752_, 0, v_toApplicative_1750_);
        crate::leanh::lean_closure_set(v___f_1752_, 1, v_x_1743_);
        v___x_1753_ = crate::leanh::lean_apply_4(
            v_toBind_1751_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_1741_,
            v___f_1752_,
        );
        return v___x_1753_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm(
    mut v_M_1754_: *mut crate::leanh::LeanObject,
    mut v_inst_1755_: *mut crate::leanh::LeanObject,
    mut v_inst_1756_: *mut crate::leanh::LeanObject,
    mut v_k_1757_: *mut crate::leanh::LeanObject,
    mut v_x_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg(v_inst_1755_, v_inst_1756_, v_k_1757_, v_x_1758_);
    return v___x_1759_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg(
    mut v_inst_1760_: *mut crate::leanh::LeanObject,
    mut v_inst_1761_: *mut crate::leanh::LeanObject,
    mut v_p_1762_: *mut crate::leanh::LeanObject,
    mut v_acc_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1762_) == 0 {
        let mut v_toApplicative_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1764_ = crate::leanh::lean_ctor_get(v_inst_1760_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1764_);
        crate::leanh::lean_dec(v_inst_1761_);
        crate::leanh::lean_dec_ref(v_inst_1760_);
        v_toPure_1765_ = crate::leanh::lean_ctor_get(v_toApplicative_1764_, 1);
        crate::leanh::lean_inc(v_toPure_1765_);
        crate::leanh::lean_dec_ref(v_toApplicative_1764_);
        v___x_1766_ =
            crate::leanh::lean_apply_2(v_toPure_1765_, crate::leanh::lean_box(0), v_acc_1763_);
        return v___x_1766_;
    } else {
        let mut v_toBind_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1767_ = crate::leanh::lean_ctor_get(v_inst_1760_, 1);
        crate::leanh::lean_inc_n(v_toBind_1767_, 2);
        v_k_1768_ = crate::leanh::lean_ctor_get(v_p_1762_, 0);
        crate::leanh::lean_inc(v_k_1768_);
        v_v_1769_ = crate::leanh::lean_ctor_get(v_p_1762_, 1);
        crate::leanh::lean_inc(v_v_1769_);
        v_p_1770_ = crate::leanh::lean_ctor_get(v_p_1762_, 2);
        crate::leanh::lean_inc(v_p_1770_);
        crate::leanh::lean_dec_ref_known(v_p_1762_, 3);
        crate::leanh::lean_inc(v_inst_1761_);
        v___f_1771_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg___lam__1 as *mut core::ffi::c_void, 8, 7);
        crate::leanh::lean_closure_set(v___f_1771_, 0, v_acc_1763_);
        crate::leanh::lean_closure_set(v___f_1771_, 1, v_inst_1760_);
        crate::leanh::lean_closure_set(v___f_1771_, 2, v_inst_1761_);
        crate::leanh::lean_closure_set(v___f_1771_, 3, v_p_1770_);
        crate::leanh::lean_closure_set(v___f_1771_, 4, v_k_1768_);
        crate::leanh::lean_closure_set(v___f_1771_, 5, v_v_1769_);
        crate::leanh::lean_closure_set(v___f_1771_, 6, v_toBind_1767_);
        v___x_1772_ = crate::leanh::lean_apply_4(
            v_toBind_1767_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_1761_,
            v___f_1771_,
        );
        return v___x_1772_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg___lam__0(
    mut v_____do__lift_1773_: *mut crate::leanh::LeanObject,
    mut v_acc_1774_: *mut crate::leanh::LeanObject,
    mut v_inst_1775_: *mut crate::leanh::LeanObject,
    mut v_inst_1776_: *mut crate::leanh::LeanObject,
    mut v_p_1777_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_addFn_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_addFn_1779_ = crate::leanh::lean_ctor_get(v_____do__lift_1773_, 22);
    crate::leanh::lean_inc_ref(v_addFn_1779_);
    crate::leanh::lean_dec_ref(v_____do__lift_1773_);
    v___x_1780_ = l_Lean_mkAppB(v_addFn_1779_, v_acc_1774_, v_____do__lift_1778_);
    v___x_1781_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg(v_inst_1775_, v_inst_1776_, v_p_1777_, v___x_1780_);
    return v___x_1781_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg___lam__1(
    mut v_acc_1782_: *mut crate::leanh::LeanObject,
    mut v_inst_1783_: *mut crate::leanh::LeanObject,
    mut v_inst_1784_: *mut crate::leanh::LeanObject,
    mut v_p_1785_: *mut crate::leanh::LeanObject,
    mut v_k_1786_: *mut crate::leanh::LeanObject,
    mut v_v_1787_: *mut crate::leanh::LeanObject,
    mut v_toBind_1788_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_1784_);
    crate::leanh::lean_inc_ref(v_inst_1783_);
    v___f_1790_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg___lam__0 as *mut core::ffi::c_void, 6, 5);
    crate::leanh::lean_closure_set(v___f_1790_, 0, v_____do__lift_1789_);
    crate::leanh::lean_closure_set(v___f_1790_, 1, v_acc_1782_);
    crate::leanh::lean_closure_set(v___f_1790_, 2, v_inst_1783_);
    crate::leanh::lean_closure_set(v___f_1790_, 3, v_inst_1784_);
    crate::leanh::lean_closure_set(v___f_1790_, 4, v_p_1785_);
    v___x_1791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg(v_inst_1783_, v_inst_1784_, v_k_1786_, v_v_1787_);
    v___x_1792_ = crate::leanh::lean_apply_4(
        v_toBind_1788_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1791_,
        v___f_1790_,
    );
    return v___x_1792_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go(
    mut v_M_1793_: *mut crate::leanh::LeanObject,
    mut v_inst_1794_: *mut crate::leanh::LeanObject,
    mut v_inst_1795_: *mut crate::leanh::LeanObject,
    mut v_p_1796_: *mut crate::leanh::LeanObject,
    mut v_acc_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1798_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg(v_inst_1794_, v_inst_1795_, v_p_1796_, v_acc_1797_);
    return v___x_1798_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteExpr___redArg___lam__0(
    mut v_toPure_1799_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zero_1801_ = crate::leanh::lean_ctor_get(v_____do__lift_1800_, 17);
    crate::leanh::lean_inc_ref(v_zero_1801_);
    crate::leanh::lean_dec_ref(v_____do__lift_1800_);
    v___x_1802_ =
        crate::leanh::lean_apply_2(v_toPure_1799_, crate::leanh::lean_box(0), v_zero_1801_);
    return v___x_1802_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteExpr___redArg___lam__1(
    mut v_inst_1803_: *mut crate::leanh::LeanObject,
    mut v_inst_1804_: *mut crate::leanh::LeanObject,
    mut v_p_1805_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_go___redArg(v_inst_1803_, v_inst_1804_, v_p_1805_, v_____do__lift_1806_);
    return v___x_1807_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteExpr___redArg(
    mut v_inst_1808_: *mut crate::leanh::LeanObject,
    mut v_inst_1809_: *mut crate::leanh::LeanObject,
    mut v_p_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1810_) == 0 {
        let mut v_toApplicative_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_1811_ = crate::leanh::lean_ctor_get(v_inst_1808_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_1811_);
        v_toBind_1812_ = crate::leanh::lean_ctor_get(v_inst_1808_, 1);
        crate::leanh::lean_inc(v_toBind_1812_);
        crate::leanh::lean_dec_ref(v_inst_1808_);
        v_toPure_1813_ = crate::leanh::lean_ctor_get(v_toApplicative_1811_, 1);
        crate::leanh::lean_inc(v_toPure_1813_);
        crate::leanh::lean_dec_ref(v_toApplicative_1811_);
        v___f_1814_ = crate::leanh::lean_alloc_closure(
            l_Lean_Grind_Linarith_Poly_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_1814_, 0, v_toPure_1813_);
        v___x_1815_ = crate::leanh::lean_apply_4(
            v_toBind_1812_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_inst_1809_,
            v___f_1814_,
        );
        return v___x_1815_;
    } else {
        let mut v_toBind_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1816_ = crate::leanh::lean_ctor_get(v_inst_1808_, 1);
        crate::leanh::lean_inc(v_toBind_1816_);
        v_k_1817_ = crate::leanh::lean_ctor_get(v_p_1810_, 0);
        crate::leanh::lean_inc(v_k_1817_);
        v_v_1818_ = crate::leanh::lean_ctor_get(v_p_1810_, 1);
        crate::leanh::lean_inc(v_v_1818_);
        v_p_1819_ = crate::leanh::lean_ctor_get(v_p_1810_, 2);
        crate::leanh::lean_inc(v_p_1819_);
        crate::leanh::lean_dec_ref_known(v_p_1810_, 3);
        crate::leanh::lean_inc(v_inst_1809_);
        crate::leanh::lean_inc_ref(v_inst_1808_);
        v___f_1820_ = crate::leanh::lean_alloc_closure(
            l_Lean_Grind_Linarith_Poly_denoteExpr___redArg___lam__1 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1820_, 0, v_inst_1808_);
        crate::leanh::lean_closure_set(v___f_1820_, 1, v_inst_1809_);
        crate::leanh::lean_closure_set(v___f_1820_, 2, v_p_1819_);
        v___x_1821_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg(v_inst_1808_, v_inst_1809_, v_k_1817_, v_v_1818_);
        v___x_1822_ = crate::leanh::lean_apply_4(
            v_toBind_1816_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1821_,
            v___f_1820_,
        );
        return v___x_1822_;
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteExpr(
    mut v_M_1823_: *mut crate::leanh::LeanObject,
    mut v_inst_1824_: *mut crate::leanh::LeanObject,
    mut v_inst_1825_: *mut crate::leanh::LeanObject,
    mut v_p_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ =
        l_Lean_Grind_Linarith_Poly_denoteExpr___redArg(v_inst_1824_, v_inst_1825_, v_p_1826_);
    return v___x_1827_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__1(
    mut v_i_1828_: *mut crate::leanh::LeanObject,
    mut v___x_1829_: *mut crate::leanh::LeanObject,
    mut v_toPure_1830_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    v_vars_1832_ = crate::leanh::lean_ctor_get(v_____do__lift_1831_, 30);
    v_size_1833_ = crate::leanh::lean_ctor_get(v_vars_1832_, 2);
    v___x_1834_ = lean_nat_dec_lt(v_i_1828_, v_size_1833_);
    if v___x_1834_ == 0 {
        let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1835_ = l_outOfBounds___redArg(v___x_1829_);
        v___x_1836_ =
            crate::leanh::lean_apply_2(v_toPure_1830_, crate::leanh::lean_box(0), v___x_1835_);
        return v___x_1836_;
    } else {
        let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1837_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1829_, v_vars_1832_, v_i_1828_);
        v___x_1838_ =
            crate::leanh::lean_apply_2(v_toPure_1830_, crate::leanh::lean_box(0), v___x_1837_);
        return v___x_1838_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__1___boxed(
    mut v_i_1839_: *mut crate::leanh::LeanObject,
    mut v___x_1840_: *mut crate::leanh::LeanObject,
    mut v_toPure_1841_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__1(v_i_1839_, v___x_1840_, v_toPure_1841_, v_____do__lift_1842_);
    crate::leanh::lean_dec_ref(v_____do__lift_1842_);
    crate::leanh::lean_dec_ref(v___x_1840_);
    crate::leanh::lean_dec(v_i_1839_);
    return v_res_1843_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__0(
    mut v_____do__lift_1844_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1845_: *mut crate::leanh::LeanObject,
    mut v_toPure_1846_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_addFn_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_addFn_1848_ = crate::leanh::lean_ctor_get(v_____do__lift_1844_, 22);
    crate::leanh::lean_inc_ref(v_addFn_1848_);
    crate::leanh::lean_dec_ref(v_____do__lift_1844_);
    v___x_1849_ = l_Lean_mkAppB(v_addFn_1848_, v_____do__lift_1845_, v_____do__lift_1847_);
    v___x_1850_ =
        crate::leanh::lean_apply_2(v_toPure_1846_, crate::leanh::lean_box(0), v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__9(
    mut v_____do__lift_1851_: *mut crate::leanh::LeanObject,
    mut v_k_1852_: *mut crate::leanh::LeanObject,
    mut v_toPure_1853_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nsmulFn_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nsmulFn_1855_ = crate::leanh::lean_ctor_get(v_____do__lift_1851_, 24);
    crate::leanh::lean_inc_ref(v_nsmulFn_1855_);
    crate::leanh::lean_dec_ref(v_____do__lift_1851_);
    v___x_1856_ = l_Lean_mkNatLit(v_k_1852_);
    v___x_1857_ = l_Lean_mkAppB(v_nsmulFn_1855_, v___x_1856_, v_____do__lift_1854_);
    v___x_1858_ =
        crate::leanh::lean_apply_2(v_toPure_1853_, crate::leanh::lean_box(0), v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__7(
    mut v_____do__lift_1859_: *mut crate::leanh::LeanObject,
    mut v_toPure_1860_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_negFn_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_negFn_1862_ = crate::leanh::lean_ctor_get(v_____do__lift_1859_, 29);
    crate::leanh::lean_inc_ref(v_negFn_1862_);
    crate::leanh::lean_dec_ref(v_____do__lift_1859_);
    v___x_1863_ = l_Lean_Expr_app___override(v_negFn_1862_, v_____do__lift_1861_);
    v___x_1864_ =
        crate::leanh::lean_apply_2(v_toPure_1860_, crate::leanh::lean_box(0), v___x_1863_);
    return v___x_1864_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__4(
    mut v_____do__lift_1865_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1866_: *mut crate::leanh::LeanObject,
    mut v_toPure_1867_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subFn_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_subFn_1869_ = crate::leanh::lean_ctor_get(v_____do__lift_1865_, 28);
    crate::leanh::lean_inc_ref(v_subFn_1869_);
    crate::leanh::lean_dec_ref(v_____do__lift_1865_);
    v___x_1870_ = l_Lean_mkAppB(v_subFn_1869_, v_____do__lift_1866_, v_____do__lift_1868_);
    v___x_1871_ =
        crate::leanh::lean_apply_2(v_toPure_1867_, crate::leanh::lean_box(0), v___x_1870_);
    return v___x_1871_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__11(
    mut v_____do__lift_1872_: *mut crate::leanh::LeanObject,
    mut v_k_1873_: *mut crate::leanh::LeanObject,
    mut v_toPure_1874_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zsmulFn_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zsmulFn_1876_ = crate::leanh::lean_ctor_get(v_____do__lift_1872_, 23);
    crate::leanh::lean_inc_ref(v_zsmulFn_1876_);
    crate::leanh::lean_dec_ref(v_____do__lift_1872_);
    v___x_1877_ = l_Lean_mkIntLit(v_k_1873_);
    v___x_1878_ = l_Lean_mkAppB(v_zsmulFn_1876_, v___x_1877_, v_____do__lift_1875_);
    v___x_1879_ =
        crate::leanh::lean_apply_2(v_toPure_1874_, crate::leanh::lean_box(0), v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__11___boxed(
    mut v_____do__lift_1880_: *mut crate::leanh::LeanObject,
    mut v_k_1881_: *mut crate::leanh::LeanObject,
    mut v_toPure_1882_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__11(v_____do__lift_1880_, v_k_1881_, v_toPure_1882_, v_____do__lift_1883_);
    crate::leanh::lean_dec(v_k_1881_);
    return v_res_1884_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__2(
    mut v_____do__lift_1885_: *mut crate::leanh::LeanObject,
    mut v_toPure_1886_: *mut crate::leanh::LeanObject,
    mut v_inst_1887_: *mut crate::leanh::LeanObject,
    mut v_inst_1888_: *mut crate::leanh::LeanObject,
    mut v_b_1889_: *mut crate::leanh::LeanObject,
    mut v_toBind_1890_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1892_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1892_, 0, v_____do__lift_1885_);
    crate::leanh::lean_closure_set(v___f_1892_, 1, v_____do__lift_1891_);
    crate::leanh::lean_closure_set(v___f_1892_, 2, v_toPure_1886_);
    v___x_1893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_1887_, v_inst_1888_, v_b_1889_);
    v___x_1894_ = crate::leanh::lean_apply_4(
        v_toBind_1890_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1893_,
        v___f_1892_,
    );
    return v___x_1894_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__3(
    mut v_toPure_1895_: *mut crate::leanh::LeanObject,
    mut v_inst_1896_: *mut crate::leanh::LeanObject,
    mut v_inst_1897_: *mut crate::leanh::LeanObject,
    mut v_b_1898_: *mut crate::leanh::LeanObject,
    mut v_toBind_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1899_);
    crate::leanh::lean_inc(v_inst_1897_);
    crate::leanh::lean_inc_ref(v_inst_1896_);
    v___f_1902_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__2 as *mut core::ffi::c_void, 7, 6);
    crate::leanh::lean_closure_set(v___f_1902_, 0, v_____do__lift_1901_);
    crate::leanh::lean_closure_set(v___f_1902_, 1, v_toPure_1895_);
    crate::leanh::lean_closure_set(v___f_1902_, 2, v_inst_1896_);
    crate::leanh::lean_closure_set(v___f_1902_, 3, v_inst_1897_);
    crate::leanh::lean_closure_set(v___f_1902_, 4, v_b_1898_);
    crate::leanh::lean_closure_set(v___f_1902_, 5, v_toBind_1899_);
    v___x_1903_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_1896_, v_inst_1897_, v_a_1900_);
    v___x_1904_ = crate::leanh::lean_apply_4(
        v_toBind_1899_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1903_,
        v___f_1902_,
    );
    return v___x_1904_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__5(
    mut v_____do__lift_1905_: *mut crate::leanh::LeanObject,
    mut v_toPure_1906_: *mut crate::leanh::LeanObject,
    mut v_inst_1907_: *mut crate::leanh::LeanObject,
    mut v_inst_1908_: *mut crate::leanh::LeanObject,
    mut v_b_1909_: *mut crate::leanh::LeanObject,
    mut v_toBind_1910_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1912_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__4 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1912_, 0, v_____do__lift_1905_);
    crate::leanh::lean_closure_set(v___f_1912_, 1, v_____do__lift_1911_);
    crate::leanh::lean_closure_set(v___f_1912_, 2, v_toPure_1906_);
    v___x_1913_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_1907_, v_inst_1908_, v_b_1909_);
    v___x_1914_ = crate::leanh::lean_apply_4(
        v_toBind_1910_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1913_,
        v___f_1912_,
    );
    return v___x_1914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__6(
    mut v_toPure_1915_: *mut crate::leanh::LeanObject,
    mut v_inst_1916_: *mut crate::leanh::LeanObject,
    mut v_inst_1917_: *mut crate::leanh::LeanObject,
    mut v_b_1918_: *mut crate::leanh::LeanObject,
    mut v_toBind_1919_: *mut crate::leanh::LeanObject,
    mut v_a_1920_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_1919_);
    crate::leanh::lean_inc(v_inst_1917_);
    crate::leanh::lean_inc_ref(v_inst_1916_);
    v___f_1922_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__5 as *mut core::ffi::c_void, 7, 6);
    crate::leanh::lean_closure_set(v___f_1922_, 0, v_____do__lift_1921_);
    crate::leanh::lean_closure_set(v___f_1922_, 1, v_toPure_1915_);
    crate::leanh::lean_closure_set(v___f_1922_, 2, v_inst_1916_);
    crate::leanh::lean_closure_set(v___f_1922_, 3, v_inst_1917_);
    crate::leanh::lean_closure_set(v___f_1922_, 4, v_b_1918_);
    crate::leanh::lean_closure_set(v___f_1922_, 5, v_toBind_1919_);
    v___x_1923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_1916_, v_inst_1917_, v_a_1920_);
    v___x_1924_ = crate::leanh::lean_apply_4(
        v_toBind_1919_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1923_,
        v___f_1922_,
    );
    return v___x_1924_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__8(
    mut v_toPure_1925_: *mut crate::leanh::LeanObject,
    mut v_inst_1926_: *mut crate::leanh::LeanObject,
    mut v_inst_1927_: *mut crate::leanh::LeanObject,
    mut v_a_1928_: *mut crate::leanh::LeanObject,
    mut v_toBind_1929_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1931_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__7 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_1931_, 0, v_____do__lift_1930_);
    crate::leanh::lean_closure_set(v___f_1931_, 1, v_toPure_1925_);
    v___x_1932_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_1926_, v_inst_1927_, v_a_1928_);
    v___x_1933_ = crate::leanh::lean_apply_4(
        v_toBind_1929_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1932_,
        v___f_1931_,
    );
    return v___x_1933_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__12(
    mut v_k_1934_: *mut crate::leanh::LeanObject,
    mut v_toPure_1935_: *mut crate::leanh::LeanObject,
    mut v_inst_1936_: *mut crate::leanh::LeanObject,
    mut v_inst_1937_: *mut crate::leanh::LeanObject,
    mut v_a_1938_: *mut crate::leanh::LeanObject,
    mut v_toBind_1939_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1941_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__11___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_1941_, 0, v_____do__lift_1940_);
    crate::leanh::lean_closure_set(v___f_1941_, 1, v_k_1934_);
    crate::leanh::lean_closure_set(v___f_1941_, 2, v_toPure_1935_);
    v___x_1942_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_1936_, v_inst_1937_, v_a_1938_);
    v___x_1943_ = crate::leanh::lean_apply_4(
        v_toBind_1939_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1942_,
        v___f_1941_,
    );
    return v___x_1943_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(
    mut v_inst_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_a_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_1946_) {
        0 => {
            let mut v_toApplicative_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1947_ = crate::leanh::lean_ctor_get(v_inst_1944_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1947_);
            v_toBind_1948_ = crate::leanh::lean_ctor_get(v_inst_1944_, 1);
            crate::leanh::lean_inc(v_toBind_1948_);
            crate::leanh::lean_dec_ref(v_inst_1944_);
            v_toPure_1949_ = crate::leanh::lean_ctor_get(v_toApplicative_1947_, 1);
            crate::leanh::lean_inc(v_toPure_1949_);
            crate::leanh::lean_dec_ref(v_toApplicative_1947_);
            v___f_1950_ = crate::leanh::lean_alloc_closure(
                l_Lean_Grind_Linarith_Poly_denoteExpr___redArg___lam__0 as *mut core::ffi::c_void,
                2,
                1,
            );
            crate::leanh::lean_closure_set(v___f_1950_, 0, v_toPure_1949_);
            v___x_1951_ = crate::leanh::lean_apply_4(
                v_toBind_1948_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1945_,
                v___f_1950_,
            );
            return v___x_1951_;
        }
        1 => {
            let mut v_toApplicative_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1952_ = crate::leanh::lean_ctor_get(v_inst_1944_, 0);
            crate::leanh::lean_inc_ref(v_toApplicative_1952_);
            v_toBind_1953_ = crate::leanh::lean_ctor_get(v_inst_1944_, 1);
            crate::leanh::lean_inc(v_toBind_1953_);
            crate::leanh::lean_dec_ref(v_inst_1944_);
            v_toPure_1954_ = crate::leanh::lean_ctor_get(v_toApplicative_1952_, 1);
            crate::leanh::lean_inc(v_toPure_1954_);
            crate::leanh::lean_dec_ref(v_toApplicative_1952_);
            v_i_1955_ = crate::leanh::lean_ctor_get(v_a_1946_, 0);
            crate::leanh::lean_inc(v_i_1955_);
            crate::leanh::lean_dec_ref_known(v_a_1946_, 1);
            v___x_1956_ = l_Lean_instInhabitedExpr;
            v___f_1957_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
            crate::leanh::lean_closure_set(v___f_1957_, 0, v_i_1955_);
            crate::leanh::lean_closure_set(v___f_1957_, 1, v___x_1956_);
            crate::leanh::lean_closure_set(v___f_1957_, 2, v_toPure_1954_);
            v___x_1958_ = crate::leanh::lean_apply_4(
                v_toBind_1953_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1945_,
                v___f_1957_,
            );
            return v___x_1958_;
        }
        2 => {
            let mut v_toApplicative_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1959_ = crate::leanh::lean_ctor_get(v_inst_1944_, 0);
            v_toBind_1960_ = crate::leanh::lean_ctor_get(v_inst_1944_, 1);
            crate::leanh::lean_inc_n(v_toBind_1960_, 2);
            v_toPure_1961_ = crate::leanh::lean_ctor_get(v_toApplicative_1959_, 1);
            crate::leanh::lean_inc(v_toPure_1961_);
            v_a_1962_ = crate::leanh::lean_ctor_get(v_a_1946_, 0);
            crate::leanh::lean_inc(v_a_1962_);
            v_b_1963_ = crate::leanh::lean_ctor_get(v_a_1946_, 1);
            crate::leanh::lean_inc(v_b_1963_);
            crate::leanh::lean_dec_ref_known(v_a_1946_, 2);
            crate::leanh::lean_inc(v_inst_1945_);
            v___f_1964_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__3 as *mut core::ffi::c_void, 7, 6);
            crate::leanh::lean_closure_set(v___f_1964_, 0, v_toPure_1961_);
            crate::leanh::lean_closure_set(v___f_1964_, 1, v_inst_1944_);
            crate::leanh::lean_closure_set(v___f_1964_, 2, v_inst_1945_);
            crate::leanh::lean_closure_set(v___f_1964_, 3, v_b_1963_);
            crate::leanh::lean_closure_set(v___f_1964_, 4, v_toBind_1960_);
            crate::leanh::lean_closure_set(v___f_1964_, 5, v_a_1962_);
            v___x_1965_ = crate::leanh::lean_apply_4(
                v_toBind_1960_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1945_,
                v___f_1964_,
            );
            return v___x_1965_;
        }
        3 => {
            let mut v_toApplicative_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1966_ = crate::leanh::lean_ctor_get(v_inst_1944_, 0);
            v_toBind_1967_ = crate::leanh::lean_ctor_get(v_inst_1944_, 1);
            crate::leanh::lean_inc_n(v_toBind_1967_, 2);
            v_toPure_1968_ = crate::leanh::lean_ctor_get(v_toApplicative_1966_, 1);
            crate::leanh::lean_inc(v_toPure_1968_);
            v_a_1969_ = crate::leanh::lean_ctor_get(v_a_1946_, 0);
            crate::leanh::lean_inc(v_a_1969_);
            v_b_1970_ = crate::leanh::lean_ctor_get(v_a_1946_, 1);
            crate::leanh::lean_inc(v_b_1970_);
            crate::leanh::lean_dec_ref_known(v_a_1946_, 2);
            crate::leanh::lean_inc(v_inst_1945_);
            v___f_1971_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__6 as *mut core::ffi::c_void, 7, 6);
            crate::leanh::lean_closure_set(v___f_1971_, 0, v_toPure_1968_);
            crate::leanh::lean_closure_set(v___f_1971_, 1, v_inst_1944_);
            crate::leanh::lean_closure_set(v___f_1971_, 2, v_inst_1945_);
            crate::leanh::lean_closure_set(v___f_1971_, 3, v_b_1970_);
            crate::leanh::lean_closure_set(v___f_1971_, 4, v_toBind_1967_);
            crate::leanh::lean_closure_set(v___f_1971_, 5, v_a_1969_);
            v___x_1972_ = crate::leanh::lean_apply_4(
                v_toBind_1967_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1945_,
                v___f_1971_,
            );
            return v___x_1972_;
        }
        4 => {
            let mut v_toApplicative_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1973_ = crate::leanh::lean_ctor_get(v_inst_1944_, 0);
            v_toBind_1974_ = crate::leanh::lean_ctor_get(v_inst_1944_, 1);
            crate::leanh::lean_inc_n(v_toBind_1974_, 2);
            v_toPure_1975_ = crate::leanh::lean_ctor_get(v_toApplicative_1973_, 1);
            crate::leanh::lean_inc(v_toPure_1975_);
            v_a_1976_ = crate::leanh::lean_ctor_get(v_a_1946_, 0);
            crate::leanh::lean_inc(v_a_1976_);
            crate::leanh::lean_dec_ref_known(v_a_1946_, 1);
            crate::leanh::lean_inc(v_inst_1945_);
            v___f_1977_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__8 as *mut core::ffi::c_void, 6, 5);
            crate::leanh::lean_closure_set(v___f_1977_, 0, v_toPure_1975_);
            crate::leanh::lean_closure_set(v___f_1977_, 1, v_inst_1944_);
            crate::leanh::lean_closure_set(v___f_1977_, 2, v_inst_1945_);
            crate::leanh::lean_closure_set(v___f_1977_, 3, v_a_1976_);
            crate::leanh::lean_closure_set(v___f_1977_, 4, v_toBind_1974_);
            v___x_1978_ = crate::leanh::lean_apply_4(
                v_toBind_1974_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1945_,
                v___f_1977_,
            );
            return v___x_1978_;
        }
        5 => {
            let mut v_toApplicative_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1979_ = crate::leanh::lean_ctor_get(v_inst_1944_, 0);
            v_toBind_1980_ = crate::leanh::lean_ctor_get(v_inst_1944_, 1);
            crate::leanh::lean_inc_n(v_toBind_1980_, 2);
            v_toPure_1981_ = crate::leanh::lean_ctor_get(v_toApplicative_1979_, 1);
            crate::leanh::lean_inc(v_toPure_1981_);
            v_k_1982_ = crate::leanh::lean_ctor_get(v_a_1946_, 0);
            crate::leanh::lean_inc(v_k_1982_);
            v_a_1983_ = crate::leanh::lean_ctor_get(v_a_1946_, 1);
            crate::leanh::lean_inc(v_a_1983_);
            crate::leanh::lean_dec_ref_known(v_a_1946_, 2);
            crate::leanh::lean_inc(v_inst_1945_);
            v___f_1984_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__10 as *mut core::ffi::c_void, 7, 6);
            crate::leanh::lean_closure_set(v___f_1984_, 0, v_k_1982_);
            crate::leanh::lean_closure_set(v___f_1984_, 1, v_toPure_1981_);
            crate::leanh::lean_closure_set(v___f_1984_, 2, v_inst_1944_);
            crate::leanh::lean_closure_set(v___f_1984_, 3, v_inst_1945_);
            crate::leanh::lean_closure_set(v___f_1984_, 4, v_a_1983_);
            crate::leanh::lean_closure_set(v___f_1984_, 5, v_toBind_1980_);
            v___x_1985_ = crate::leanh::lean_apply_4(
                v_toBind_1980_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1945_,
                v___f_1984_,
            );
            return v___x_1985_;
        }
        _ => {
            let mut v_toApplicative_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_toPure_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toApplicative_1986_ = crate::leanh::lean_ctor_get(v_inst_1944_, 0);
            v_toBind_1987_ = crate::leanh::lean_ctor_get(v_inst_1944_, 1);
            crate::leanh::lean_inc_n(v_toBind_1987_, 2);
            v_toPure_1988_ = crate::leanh::lean_ctor_get(v_toApplicative_1986_, 1);
            crate::leanh::lean_inc(v_toPure_1988_);
            v_k_1989_ = crate::leanh::lean_ctor_get(v_a_1946_, 0);
            crate::leanh::lean_inc(v_k_1989_);
            v_a_1990_ = crate::leanh::lean_ctor_get(v_a_1946_, 1);
            crate::leanh::lean_inc(v_a_1990_);
            crate::leanh::lean_dec_ref_known(v_a_1946_, 2);
            crate::leanh::lean_inc(v_inst_1945_);
            v___f_1991_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__12 as *mut core::ffi::c_void, 7, 6);
            crate::leanh::lean_closure_set(v___f_1991_, 0, v_k_1989_);
            crate::leanh::lean_closure_set(v___f_1991_, 1, v_toPure_1988_);
            crate::leanh::lean_closure_set(v___f_1991_, 2, v_inst_1944_);
            crate::leanh::lean_closure_set(v___f_1991_, 3, v_inst_1945_);
            crate::leanh::lean_closure_set(v___f_1991_, 4, v_a_1990_);
            crate::leanh::lean_closure_set(v___f_1991_, 5, v_toBind_1987_);
            v___x_1992_ = crate::leanh::lean_apply_4(
                v_toBind_1987_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v_inst_1945_,
                v___f_1991_,
            );
            return v___x_1992_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__10(
    mut v_k_1993_: *mut crate::leanh::LeanObject,
    mut v_toPure_1994_: *mut crate::leanh::LeanObject,
    mut v_inst_1995_: *mut crate::leanh::LeanObject,
    mut v_inst_1996_: *mut crate::leanh::LeanObject,
    mut v_a_1997_: *mut crate::leanh::LeanObject,
    mut v_toBind_1998_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2000_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg___lam__9 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_2000_, 0, v_____do__lift_1999_);
    crate::leanh::lean_closure_set(v___f_2000_, 1, v_k_1993_);
    crate::leanh::lean_closure_set(v___f_2000_, 2, v_toPure_1994_);
    v___x_2001_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_1995_, v_inst_1996_, v_a_1997_);
    v___x_2002_ = crate::leanh::lean_apply_4(
        v_toBind_1998_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2001_,
        v___f_2000_,
    );
    return v___x_2002_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go(
    mut v_M_2003_: *mut crate::leanh::LeanObject,
    mut v_inst_2004_: *mut crate::leanh::LeanObject,
    mut v_inst_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_2004_, v_inst_2005_, v_a_2006_);
    return v___x_2007_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denoteExpr___redArg(
    mut v_inst_2008_: *mut crate::leanh::LeanObject,
    mut v_inst_2009_: *mut crate::leanh::LeanObject,
    mut v_e_2010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2011_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_2008_, v_inst_2009_, v_e_2010_);
    return v___x_2011_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denoteExpr(
    mut v_M_2012_: *mut crate::leanh::LeanObject,
    mut v_inst_2013_: *mut crate::leanh::LeanObject,
    mut v_inst_2014_: *mut crate::leanh::LeanObject,
    mut v_e_2015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Expr_denoteExpr_go___redArg(v_inst_2013_, v_inst_2014_, v_e_2015_);
    return v___x_2016_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0(
    mut v_a_2020_: *mut crate::leanh::LeanObject,
    mut v_b_2021_: *mut crate::leanh::LeanObject,
    mut v_toPure_2022_: *mut crate::leanh::LeanObject,
    mut v_s_2023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_2024_ = crate::leanh::lean_ctor_get(v_s_2023_, 2);
    crate::leanh::lean_inc_ref(v_type_2024_);
    v_u_2025_ = crate::leanh::lean_ctor_get(v_s_2023_, 3);
    crate::leanh::lean_inc(v_u_2025_);
    crate::leanh::lean_dec_ref(v_s_2023_);
    v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0___closed__1;
    v___x_2027_ = l_Lean_Level_succ___override(v_u_2025_);
    v___x_2028_ = crate::leanh::lean_box(0);
    v___x_2029_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2029_, 0, v___x_2027_);
    crate::leanh::lean_ctor_set(v___x_2029_, 1, v___x_2028_);
    v___x_2030_ = l_Lean_mkConst(v___x_2026_, v___x_2029_);
    v___x_2031_ = l_Lean_mkApp3(v___x_2030_, v_type_2024_, v_a_2020_, v_b_2021_);
    v___x_2032_ =
        crate::leanh::lean_apply_2(v_toPure_2022_, crate::leanh::lean_box(0), v___x_2031_);
    return v___x_2032_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg(
    mut v_inst_2033_: *mut crate::leanh::LeanObject,
    mut v_inst_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_b_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2037_ = crate::leanh::lean_ctor_get(v_inst_2033_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2037_);
    v_toBind_2038_ = crate::leanh::lean_ctor_get(v_inst_2033_, 1);
    crate::leanh::lean_inc(v_toBind_2038_);
    crate::leanh::lean_dec_ref(v_inst_2033_);
    v_toPure_2039_ = crate::leanh::lean_ctor_get(v_toApplicative_2037_, 1);
    crate::leanh::lean_inc(v_toPure_2039_);
    crate::leanh::lean_dec_ref(v_toApplicative_2037_);
    v___f_2040_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_2040_, 0, v_a_2035_);
    crate::leanh::lean_closure_set(v___f_2040_, 1, v_b_2036_);
    crate::leanh::lean_closure_set(v___f_2040_, 2, v_toPure_2039_);
    v___x_2041_ = crate::leanh::lean_apply_4(
        v_toBind_2038_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2034_,
        v___f_2040_,
    );
    return v___x_2041_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq(
    mut v_M_2042_: *mut crate::leanh::LeanObject,
    mut v_inst_2043_: *mut crate::leanh::LeanObject,
    mut v_inst_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_b_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2047_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg(v_inst_2043_, v_inst_2044_, v_a_2045_, v_b_2046_);
    return v___x_2047_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg___lam__0(
    mut v_toPure_2048_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_Lean_mkNot(v_____do__lift_2049_);
    v___x_2051_ =
        crate::leanh::lean_apply_2(v_toPure_2048_, crate::leanh::lean_box(0), v___x_2050_);
    return v___x_2051_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg___lam__1(
    mut v_inst_2052_: *mut crate::leanh::LeanObject,
    mut v_inst_2053_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2054_: *mut crate::leanh::LeanObject,
    mut v_toBind_2055_: *mut crate::leanh::LeanObject,
    mut v___f_2056_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ofNatZero_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ofNatZero_2058_ = crate::leanh::lean_ctor_get(v_____do__lift_2057_, 18);
    crate::leanh::lean_inc_ref(v_ofNatZero_2058_);
    crate::leanh::lean_dec_ref(v_____do__lift_2057_);
    v___x_2059_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg(v_inst_2052_, v_inst_2053_, v_____do__lift_2054_, v_ofNatZero_2058_);
    v___x_2060_ = crate::leanh::lean_apply_4(
        v_toBind_2055_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2059_,
        v___f_2056_,
    );
    return v___x_2060_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg___lam__2(
    mut v_inst_2061_: *mut crate::leanh::LeanObject,
    mut v_inst_2062_: *mut crate::leanh::LeanObject,
    mut v_toBind_2063_: *mut crate::leanh::LeanObject,
    mut v___f_2064_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_2063_);
    crate::leanh::lean_inc(v_inst_2062_);
    v___f_2066_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2066_, 0, v_inst_2061_);
    crate::leanh::lean_closure_set(v___f_2066_, 1, v_inst_2062_);
    crate::leanh::lean_closure_set(v___f_2066_, 2, v_____do__lift_2065_);
    crate::leanh::lean_closure_set(v___f_2066_, 3, v_toBind_2063_);
    crate::leanh::lean_closure_set(v___f_2066_, 4, v___f_2064_);
    v___x_2067_ = crate::leanh::lean_apply_4(
        v_toBind_2063_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2062_,
        v___f_2066_,
    );
    return v___x_2067_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg(
    mut v_inst_2068_: *mut crate::leanh::LeanObject,
    mut v_inst_2069_: *mut crate::leanh::LeanObject,
    mut v_c_2070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2071_ = crate::leanh::lean_ctor_get(v_inst_2068_, 0);
    v_toBind_2072_ = crate::leanh::lean_ctor_get(v_inst_2068_, 1);
    crate::leanh::lean_inc_n(v_toBind_2072_, 2);
    v_p_2073_ = crate::leanh::lean_ctor_get(v_c_2070_, 0);
    crate::leanh::lean_inc(v_p_2073_);
    crate::leanh::lean_dec_ref(v_c_2070_);
    v_toPure_2074_ = crate::leanh::lean_ctor_get(v_toApplicative_2071_, 1);
    crate::leanh::lean_inc(v_inst_2069_);
    crate::leanh::lean_inc_ref(v_inst_2068_);
    v___x_2075_ =
        l_Lean_Grind_Linarith_Poly_denoteExpr___redArg(v_inst_2068_, v_inst_2069_, v_p_2073_);
    crate::leanh::lean_inc(v_toPure_2074_);
    v___f_2076_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2076_, 0, v_toPure_2074_);
    v___f_2077_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2077_, 0, v_inst_2068_);
    crate::leanh::lean_closure_set(v___f_2077_, 1, v_inst_2069_);
    crate::leanh::lean_closure_set(v___f_2077_, 2, v_toBind_2072_);
    crate::leanh::lean_closure_set(v___f_2077_, 3, v___f_2076_);
    v___x_2078_ = crate::leanh::lean_apply_4(
        v_toBind_2072_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2075_,
        v___f_2077_,
    );
    return v___x_2078_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr(
    mut v_M_2079_: *mut crate::leanh::LeanObject,
    mut v_inst_2080_: *mut crate::leanh::LeanObject,
    mut v_inst_2081_: *mut crate::leanh::LeanObject,
    mut v_c_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_denoteExpr___redArg(
        v_inst_2080_,
        v_inst_2081_,
        v_c_2082_,
    );
    return v___x_2083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___lam__0(
    mut v_toApplicative_2084_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2085_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2086_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toPure_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toPure_2088_ = crate::leanh::lean_ctor_get(v_toApplicative_2084_, 1);
    crate::leanh::lean_inc(v_toPure_2088_);
    crate::leanh::lean_dec_ref(v_toApplicative_2084_);
    v_ofNatZero_2089_ = crate::leanh::lean_ctor_get(v_____do__lift_2087_, 18);
    crate::leanh::lean_inc_ref(v_ofNatZero_2089_);
    crate::leanh::lean_dec_ref(v_____do__lift_2087_);
    v___x_2090_ = l_Lean_mkAppB(
        v_____do__lift_2085_,
        v_____do__lift_2086_,
        v_ofNatZero_2089_,
    );
    v___x_2091_ =
        crate::leanh::lean_apply_2(v_toPure_2088_, crate::leanh::lean_box(0), v___x_2090_);
    return v___x_2091_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___lam__1(
    mut v_toApplicative_2092_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2093_: *mut crate::leanh::LeanObject,
    mut v_toBind_2094_: *mut crate::leanh::LeanObject,
    mut v_inst_2095_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2097_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___f_2097_, 0, v_toApplicative_2092_);
    crate::leanh::lean_closure_set(v___f_2097_, 1, v_____do__lift_2093_);
    crate::leanh::lean_closure_set(v___f_2097_, 2, v_____do__lift_2096_);
    v___x_2098_ = crate::leanh::lean_apply_4(
        v_toBind_2094_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2095_,
        v___f_2097_,
    );
    return v___x_2098_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___lam__2(
    mut v_toApplicative_2099_: *mut crate::leanh::LeanObject,
    mut v_toBind_2100_: *mut crate::leanh::LeanObject,
    mut v_inst_2101_: *mut crate::leanh::LeanObject,
    mut v_inst_2102_: *mut crate::leanh::LeanObject,
    mut v_p_2103_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_2101_);
    crate::leanh::lean_inc(v_toBind_2100_);
    v___f_2105_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___f_2105_, 0, v_toApplicative_2099_);
    crate::leanh::lean_closure_set(v___f_2105_, 1, v_____do__lift_2104_);
    crate::leanh::lean_closure_set(v___f_2105_, 2, v_toBind_2100_);
    crate::leanh::lean_closure_set(v___f_2105_, 3, v_inst_2101_);
    v___x_2106_ =
        l_Lean_Grind_Linarith_Poly_denoteExpr___redArg(v_inst_2102_, v_inst_2101_, v_p_2103_);
    v___x_2107_ = crate::leanh::lean_apply_4(
        v_toBind_2100_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2106_,
        v___f_2105_,
    );
    return v___x_2107_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg(
    mut v_inst_2108_: *mut crate::leanh::LeanObject,
    mut v_inst_2109_: *mut crate::leanh::LeanObject,
    mut v_inst_2110_: *mut crate::leanh::LeanObject,
    mut v_p_2111_: *mut crate::leanh::LeanObject,
    mut v_strict_2112_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_strict_2112_ == 0 {
        let mut v_toApplicative_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_2113_ = crate::leanh::lean_ctor_get(v_inst_2108_, 0);
        v_toBind_2114_ = crate::leanh::lean_ctor_get(v_inst_2108_, 1);
        crate::leanh::lean_inc_n(v_toBind_2114_, 2);
        crate::leanh::lean_inc_ref(v_inst_2108_);
        crate::leanh::lean_inc(v_inst_2109_);
        crate::leanh::lean_inc_ref(v_toApplicative_2113_);
        v___f_2115_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___lam__2 as *mut core::ffi::c_void, 6, 5);
        crate::leanh::lean_closure_set(v___f_2115_, 0, v_toApplicative_2113_);
        crate::leanh::lean_closure_set(v___f_2115_, 1, v_toBind_2114_);
        crate::leanh::lean_closure_set(v___f_2115_, 2, v_inst_2109_);
        crate::leanh::lean_closure_set(v___f_2115_, 3, v_inst_2108_);
        crate::leanh::lean_closure_set(v___f_2115_, 4, v_p_2111_);
        v___x_2116_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(
            v_inst_2108_,
            v_inst_2110_,
            v_inst_2109_,
        );
        v___x_2117_ = crate::leanh::lean_apply_4(
            v_toBind_2114_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2116_,
            v___f_2115_,
        );
        return v___x_2117_;
    } else {
        let mut v_toApplicative_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_2118_ = crate::leanh::lean_ctor_get(v_inst_2108_, 0);
        v_toBind_2119_ = crate::leanh::lean_ctor_get(v_inst_2108_, 1);
        crate::leanh::lean_inc_n(v_toBind_2119_, 2);
        crate::leanh::lean_inc_ref(v_inst_2108_);
        crate::leanh::lean_inc(v_inst_2109_);
        crate::leanh::lean_inc_ref(v_toApplicative_2118_);
        v___f_2120_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___lam__2 as *mut core::ffi::c_void, 6, 5);
        crate::leanh::lean_closure_set(v___f_2120_, 0, v_toApplicative_2118_);
        crate::leanh::lean_closure_set(v___f_2120_, 1, v_toBind_2119_);
        crate::leanh::lean_closure_set(v___f_2120_, 2, v_inst_2109_);
        crate::leanh::lean_closure_set(v___f_2120_, 3, v_inst_2108_);
        crate::leanh::lean_closure_set(v___f_2120_, 4, v_p_2111_);
        v___x_2121_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(
            v_inst_2108_,
            v_inst_2110_,
            v_inst_2109_,
        );
        v___x_2122_ = crate::leanh::lean_apply_4(
            v_toBind_2119_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2121_,
            v___f_2120_,
        );
        return v___x_2122_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg___boxed(
    mut v_inst_2123_: *mut crate::leanh::LeanObject,
    mut v_inst_2124_: *mut crate::leanh::LeanObject,
    mut v_inst_2125_: *mut crate::leanh::LeanObject,
    mut v_p_2126_: *mut crate::leanh::LeanObject,
    mut v_strict_2127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_strict_boxed_2128_: u8 = 0;
    let mut v_res_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_strict_boxed_2128_ = (crate::leanh::lean_unbox(v_strict_2127_) as u8);
    v_res_2129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg(v_inst_2123_, v_inst_2124_, v_inst_2125_, v_p_2126_, v_strict_boxed_2128_);
    return v_res_2129_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq(
    mut v_M_2130_: *mut crate::leanh::LeanObject,
    mut v_inst_2131_: *mut crate::leanh::LeanObject,
    mut v_inst_2132_: *mut crate::leanh::LeanObject,
    mut v_inst_2133_: *mut crate::leanh::LeanObject,
    mut v_p_2134_: *mut crate::leanh::LeanObject,
    mut v_strict_2135_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2136_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg(v_inst_2131_, v_inst_2132_, v_inst_2133_, v_p_2134_, v_strict_2135_);
    return v___x_2136_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___boxed(
    mut v_M_2137_: *mut crate::leanh::LeanObject,
    mut v_inst_2138_: *mut crate::leanh::LeanObject,
    mut v_inst_2139_: *mut crate::leanh::LeanObject,
    mut v_inst_2140_: *mut crate::leanh::LeanObject,
    mut v_p_2141_: *mut crate::leanh::LeanObject,
    mut v_strict_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_strict_boxed_2143_: u8 = 0;
    let mut v_res_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_strict_boxed_2143_ = (crate::leanh::lean_unbox(v_strict_2142_) as u8);
    v_res_2144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq(v_M_2137_, v_inst_2138_, v_inst_2139_, v_inst_2140_, v_p_2141_, v_strict_boxed_2143_);
    return v_res_2144_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___redArg(
    mut v_inst_2145_: *mut crate::leanh::LeanObject,
    mut v_inst_2146_: *mut crate::leanh::LeanObject,
    mut v_inst_2147_: *mut crate::leanh::LeanObject,
    mut v_c_2148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_strict_2150_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_p_2149_ = crate::leanh::lean_ctor_get(v_c_2148_, 0);
    crate::leanh::lean_inc(v_p_2149_);
    v_strict_2150_ = crate::leanh::lean_ctor_get_uint8(
        v_c_2148_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    crate::leanh::lean_dec_ref(v_c_2148_);
    v___x_2151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteIneq___redArg(v_inst_2145_, v_inst_2146_, v_inst_2147_, v_p_2149_, v_strict_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr(
    mut v_M_2152_: *mut crate::leanh::LeanObject,
    mut v_inst_2153_: *mut crate::leanh::LeanObject,
    mut v_inst_2154_: *mut crate::leanh::LeanObject,
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
    mut v_c_2156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2157_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_denoteExpr___redArg(
        v_inst_2153_,
        v_inst_2154_,
        v_inst_2155_,
        v_c_2156_,
    );
    return v___x_2157_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___redArg___lam__0(
    mut v_inst_2158_: *mut crate::leanh::LeanObject,
    mut v_inst_2159_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2160_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ofNatZero_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ofNatZero_2162_ = crate::leanh::lean_ctor_get(v_____do__lift_2161_, 18);
    crate::leanh::lean_inc_ref(v_ofNatZero_2162_);
    crate::leanh::lean_dec_ref(v_____do__lift_2161_);
    v___x_2163_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_mkEq___redArg(v_inst_2158_, v_inst_2159_, v_____do__lift_2160_, v_ofNatZero_2162_);
    return v___x_2163_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___redArg___lam__1(
    mut v_inst_2164_: *mut crate::leanh::LeanObject,
    mut v_inst_2165_: *mut crate::leanh::LeanObject,
    mut v_toBind_2166_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_2165_);
    v___f_2168_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2168_, 0, v_inst_2164_);
    crate::leanh::lean_closure_set(v___f_2168_, 1, v_inst_2165_);
    crate::leanh::lean_closure_set(v___f_2168_, 2, v_____do__lift_2167_);
    v___x_2169_ = crate::leanh::lean_apply_4(
        v_toBind_2166_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_2165_,
        v___f_2168_,
    );
    return v___x_2169_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___redArg(
    mut v_inst_2170_: *mut crate::leanh::LeanObject,
    mut v_inst_2171_: *mut crate::leanh::LeanObject,
    mut v_c_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2173_ = crate::leanh::lean_ctor_get(v_inst_2170_, 1);
    crate::leanh::lean_inc_n(v_toBind_2173_, 2);
    v_p_2174_ = crate::leanh::lean_ctor_get(v_c_2172_, 0);
    crate::leanh::lean_inc(v_p_2174_);
    crate::leanh::lean_dec_ref(v_c_2172_);
    crate::leanh::lean_inc(v_inst_2171_);
    crate::leanh::lean_inc_ref(v_inst_2170_);
    v___f_2175_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2175_, 0, v_inst_2170_);
    crate::leanh::lean_closure_set(v___f_2175_, 1, v_inst_2171_);
    crate::leanh::lean_closure_set(v___f_2175_, 2, v_toBind_2173_);
    v___x_2176_ =
        l_Lean_Grind_Linarith_Poly_denoteExpr___redArg(v_inst_2170_, v_inst_2171_, v_p_2174_);
    v___x_2177_ = crate::leanh::lean_apply_4(
        v_toBind_2173_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2176_,
        v___f_2175_,
    );
    return v___x_2177_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr(
    mut v_M_2178_: *mut crate::leanh::LeanObject,
    mut v_inst_2179_: *mut crate::leanh::LeanObject,
    mut v_inst_2180_: *mut crate::leanh::LeanObject,
    mut v_c_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstr_denoteExpr___redArg(
        v_inst_2179_,
        v_inst_2180_,
        v_c_2181_,
    );
    return v___x_2182_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteNum(
    mut v_k_2183_: *mut crate::leanh::LeanObject,
    mut v_a_2184_: *mut crate::leanh::LeanObject,
    mut v_a_2185_: *mut crate::leanh::LeanObject,
    mut v_a_2186_: *mut crate::leanh::LeanObject,
    mut v_a_2187_: *mut crate::leanh::LeanObject,
    mut v_a_2188_: *mut crate::leanh::LeanObject,
    mut v_a_2189_: *mut crate::leanh::LeanObject,
    mut v_a_2190_: *mut crate::leanh::LeanObject,
    mut v_a_2191_: *mut crate::leanh::LeanObject,
    mut v_a_2192_: *mut crate::leanh::LeanObject,
    mut v_a_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v_zsmulFn_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_a_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2196_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_,
                    v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_,
                );
                if crate::leanh::lean_obj_tag(v___x_2196_) == 0 {
                    v_a_2197_ = crate::leanh::lean_ctor_get(v___x_2196_, 0);
                    crate::leanh::lean_inc(v_a_2197_);
                    crate::leanh::lean_dec_ref_known(v___x_2196_, 1);
                    v___x_2198_ = l_Lean_Meta_Grind_Arith_Linear_getOne(
                        v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_,
                        v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2198_) == 0 {
                        v_a_2199_ = crate::leanh::lean_ctor_get(v___x_2198_, 0);
                        v_isSharedCheck_2209_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2198_)) as u8;
                        if v_isSharedCheck_2209_ == 0 {
                            v___x_2201_ = v___x_2198_;
                            v_isShared_2202_ = v_isSharedCheck_2209_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2199_);
                            crate::leanh::lean_dec(v___x_2198_);
                            v___x_2201_ = crate::leanh::lean_box(0);
                            v_isShared_2202_ = v_isSharedCheck_2209_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2197_);
                        return v___x_2198_;
                    }
                } else {
                    v_a_2210_ = crate::leanh::lean_ctor_get(v___x_2196_, 0);
                    v_isSharedCheck_2217_ = (!crate::leanh::lean_is_exclusive(v___x_2196_)) as u8;
                    if v_isSharedCheck_2217_ == 0 {
                        v___x_2212_ = v___x_2196_;
                        v_isShared_2213_ = v_isSharedCheck_2217_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2210_);
                        crate::leanh::lean_dec(v___x_2196_);
                        v___x_2212_ = crate::leanh::lean_box(0);
                        v_isShared_2213_ = v_isSharedCheck_2217_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_zsmulFn_2203_ = crate::leanh::lean_ctor_get(v_a_2197_, 23);
                crate::leanh::lean_inc_ref(v_zsmulFn_2203_);
                crate::leanh::lean_dec(v_a_2197_);
                v___x_2204_ = l_Lean_mkIntLit(v_k_2183_);
                v___x_2205_ = l_Lean_mkAppB(v_zsmulFn_2203_, v___x_2204_, v_a_2199_);
                if v_isShared_2202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2201_, 0, v___x_2205_);
                    v___x_2207_ = v___x_2201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2207_;
            }
            3 => {
                if v_isShared_2213_ == 0 {
                    v___x_2215_ = v___x_2212_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
                    v___x_2215_ = v_reuseFailAlloc_2216_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteNum___boxed(
    mut v_k_2218_: *mut crate::leanh::LeanObject,
    mut v_a_2219_: *mut crate::leanh::LeanObject,
    mut v_a_2220_: *mut crate::leanh::LeanObject,
    mut v_a_2221_: *mut crate::leanh::LeanObject,
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_a_2223_: *mut crate::leanh::LeanObject,
    mut v_a_2224_: *mut crate::leanh::LeanObject,
    mut v_a_2225_: *mut crate::leanh::LeanObject,
    mut v_a_2226_: *mut crate::leanh::LeanObject,
    mut v_a_2227_: *mut crate::leanh::LeanObject,
    mut v_a_2228_: *mut crate::leanh::LeanObject,
    mut v_a_2229_: *mut crate::leanh::LeanObject,
    mut v_a_2230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2231_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteNum(v_k_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
    crate::leanh::lean_dec(v_a_2229_);
    crate::leanh::lean_dec_ref(v_a_2228_);
    crate::leanh::lean_dec(v_a_2227_);
    crate::leanh::lean_dec_ref(v_a_2226_);
    crate::leanh::lean_dec(v_a_2225_);
    crate::leanh::lean_dec_ref(v_a_2224_);
    crate::leanh::lean_dec(v_a_2223_);
    crate::leanh::lean_dec_ref(v_a_2222_);
    crate::leanh::lean_dec(v_a_2221_);
    crate::leanh::lean_dec(v_a_2220_);
    crate::leanh::lean_dec(v_a_2219_);
    crate::leanh::lean_dec(v_k_2218_);
    return v_res_2231_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8_spec__11(
    mut v_msgData_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_st_ref_get(v___y_2236_);
    v_env_2239_ = crate::leanh::lean_ctor_get(v___x_2238_, 0);
    crate::leanh::lean_inc_ref(v_env_2239_);
    crate::leanh::lean_dec(v___x_2238_);
    v___x_2240_ = lean_st_ref_get(v___y_2234_);
    v_mctx_2241_ = crate::leanh::lean_ctor_get(v___x_2240_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2241_);
    crate::leanh::lean_dec(v___x_2240_);
    v_lctx_2242_ = crate::leanh::lean_ctor_get(v___y_2233_, 2);
    v_options_2243_ = crate::leanh::lean_ctor_get(v___y_2235_, 2);
    crate::leanh::lean_inc_ref(v_options_2243_);
    crate::leanh::lean_inc_ref(v_lctx_2242_);
    v___x_2244_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2244_, 0, v_env_2239_);
    crate::leanh::lean_ctor_set(v___x_2244_, 1, v_mctx_2241_);
    crate::leanh::lean_ctor_set(v___x_2244_, 2, v_lctx_2242_);
    crate::leanh::lean_ctor_set(v___x_2244_, 3, v_options_2243_);
    v___x_2245_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    crate::leanh::lean_ctor_set(v___x_2245_, 1, v_msgData_2232_);
    v___x_2246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2246_, 0, v___x_2245_);
    return v___x_2246_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8_spec__11___boxed(
    mut v_msgData_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8_spec__11(v_msgData_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
    crate::leanh::lean_dec(v___y_2251_);
    crate::leanh::lean_dec_ref(v___y_2250_);
    crate::leanh::lean_dec(v___y_2249_);
    crate::leanh::lean_dec_ref(v___y_2248_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8___redArg(
    mut v_msg_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2260_ = crate::leanh::lean_ctor_get(v___y_2257_, 5);
                v___x_2261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8_spec__11(v_msg_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
                v_a_2262_ = crate::leanh::lean_ctor_get(v___x_2261_, 0);
                v_isSharedCheck_2270_ = (!crate::leanh::lean_is_exclusive(v___x_2261_)) as u8;
                if v_isSharedCheck_2270_ == 0 {
                    v___x_2264_ = v___x_2261_;
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2262_);
                    crate::leanh::lean_dec(v___x_2261_);
                    v___x_2264_ = crate::leanh::lean_box(0);
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2260_);
                v___x_2266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2266_, 0, v_ref_2260_);
                crate::leanh::lean_ctor_set(v___x_2266_, 1, v_a_2262_);
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2264_, 1);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8___redArg___boxed(
    mut v_msg_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8___redArg(v_msg_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
    crate::leanh::lean_dec(v___y_2275_);
    crate::leanh::lean_dec_ref(v___y_2274_);
    crate::leanh::lean_dec(v___y_2273_);
    crate::leanh::lean_dec_ref(v___y_2272_);
    return v_res_2277_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2279_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__0;
    v___x_2280_ = l_Lean_stringToMessageData(v___x_2279_);
    return v___x_2280_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5(
    mut v_type_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
    mut v___y_2285_: *mut crate::leanh::LeanObject,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v_val_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2307_: u8 = 0;
    let mut v_a_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2281_);
                v___x_2294_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_type_2281_,
                    v___y_2289_,
                    v___y_2290_,
                    v___y_2291_,
                    v___y_2292_,
                );
                if crate::leanh::lean_obj_tag(v___x_2294_) == 0 {
                    v_a_2295_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2307_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2307_ == 0 {
                        v___x_2297_ = v___x_2294_;
                        v_isShared_2298_ = v_isSharedCheck_2307_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2295_);
                        crate::leanh::lean_dec(v___x_2294_);
                        v___x_2297_ = crate::leanh::lean_box(0);
                        v_isShared_2298_ = v_isSharedCheck_2307_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2281_);
                    v_a_2308_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2315_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2315_ == 0 {
                        v___x_2310_ = v___x_2294_;
                        v_isShared_2311_ = v_isSharedCheck_2315_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2308_);
                        crate::leanh::lean_dec(v___x_2294_);
                        v___x_2310_ = crate::leanh::lean_box(0);
                        v_isShared_2311_ = v_isSharedCheck_2315_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2295_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_2281_);
                    v_val_2299_ = crate::leanh::lean_ctor_get(v_a_2295_, 0);
                    crate::leanh::lean_inc(v_val_2299_);
                    crate::leanh::lean_dec_ref_known(v_a_2295_, 1);
                    if v_isShared_2298_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2297_, 0, v_val_2299_);
                        v___x_2301_ = v___x_2297_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_val_2299_);
                        v___x_2301_ = v_reuseFailAlloc_2302_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2297_);
                    crate::leanh::lean_dec(v_a_2295_);
                    v___x_2303_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__1_once), _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___closed__1);
                    v___x_2304_ = l_Lean_indentExpr(v_type_2281_);
                    v___x_2305_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2305_, 0, v___x_2303_);
                    crate::leanh::lean_ctor_set(v___x_2305_, 1, v___x_2304_);
                    v___x_2306_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8___redArg(v___x_2305_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
                    return v___x_2306_;
                }
            }
            2 => {
                return v___x_2301_;
            }
            3 => {
                if v_isShared_2311_ == 0 {
                    v___x_2313_ = v___x_2310_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2314_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
                    v___x_2313_ = v_reuseFailAlloc_2314_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5___boxed(
    mut v_type_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
    mut v___y_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
    mut v___y_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5(v_type_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
    crate::leanh::lean_dec(v___y_2327_);
    crate::leanh::lean_dec_ref(v___y_2326_);
    crate::leanh::lean_dec(v___y_2325_);
    crate::leanh::lean_dec_ref(v___y_2324_);
    crate::leanh::lean_dec(v___y_2323_);
    crate::leanh::lean_dec_ref(v___y_2322_);
    crate::leanh::lean_dec(v___y_2321_);
    crate::leanh::lean_dec_ref(v___y_2320_);
    crate::leanh::lean_dec(v___y_2319_);
    crate::leanh::lean_dec(v___y_2318_);
    crate::leanh::lean_dec(v___y_2317_);
    return v_res_2329_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2334_ = l_Lean_Level_ofNat(v___x_2333_);
    return v___x_2334_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5(
    mut v_u_2348_: *mut crate::leanh::LeanObject,
    mut v_type_2349_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inst_x27_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2387_: u8 = 0;
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2363_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__1;
                v___x_2364_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__2_once), _init_l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__2);
                v___x_2365_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_u_2348_);
                v___x_2366_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2366_, 0, v_u_2348_);
                crate::leanh::lean_ctor_set(v___x_2366_, 1, v___x_2365_);
                crate::leanh::lean_inc_ref(v___x_2366_);
                v___x_2367_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2367_, 0, v___x_2364_);
                crate::leanh::lean_ctor_set(v___x_2367_, 1, v___x_2366_);
                v___x_2368_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2368_, 0, v_u_2348_);
                crate::leanh::lean_ctor_set(v___x_2368_, 1, v___x_2367_);
                crate::leanh::lean_inc_ref(v___x_2368_);
                v___x_2369_ = l_Lean_mkConst(v___x_2363_, v___x_2368_);
                v___x_2370_ = l_Lean_Nat_mkType;
                crate::leanh::lean_inc_ref_n(v_type_2349_, 2);
                v___x_2371_ = l_Lean_mkApp3(v___x_2369_, v_type_2349_, v___x_2370_, v_type_2349_);
                v___x_2372_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5(v___x_2371_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
                if crate::leanh::lean_obj_tag(v___x_2372_) == 0 {
                    v_a_2373_ = crate::leanh::lean_ctor_get(v___x_2372_, 0);
                    crate::leanh::lean_inc_n(v_a_2373_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2372_, 1);
                    v___x_2374_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__7;
                    v___x_2375_ = l_Lean_mkConst(v___x_2374_, v___x_2366_);
                    crate::leanh::lean_inc_ref(v_type_2349_);
                    v_inst_x27_2376_ =
                        l_Lean_mkAppB(v___x_2375_, v_type_2349_, v_semiringInst_2350_);
                    v___x_2377_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___closed__9;
                    v___x_2378_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v___x_2377_,
                        v_a_2373_,
                        v_inst_x27_2376_,
                        v___y_2358_,
                        v___y_2359_,
                        v___y_2360_,
                        v___y_2361_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2378_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2378_, 1);
                        v___x_2379_ = l_Lean_mkConst(v___x_2377_, v___x_2368_);
                        crate::leanh::lean_inc_ref(v_type_2349_);
                        v___x_2380_ = l_Lean_mkApp4(
                            v___x_2379_,
                            v_type_2349_,
                            v___x_2370_,
                            v_type_2349_,
                            v_a_2373_,
                        );
                        v___x_2381_ = l_Lean_Meta_Sym_canon(
                            v___x_2380_,
                            v___y_2356_,
                            v___y_2357_,
                            v___y_2358_,
                            v___y_2359_,
                            v___y_2360_,
                            v___y_2361_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2381_) == 0 {
                            v_a_2382_ = crate::leanh::lean_ctor_get(v___x_2381_, 0);
                            crate::leanh::lean_inc(v_a_2382_);
                            crate::leanh::lean_dec_ref_known(v___x_2381_, 1);
                            v___x_2383_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_2382_, v___y_2357_);
                            return v___x_2383_;
                        } else {
                            return v___x_2381_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2373_);
                        crate::leanh::lean_dec_ref_known(v___x_2368_, 2);
                        crate::leanh::lean_dec_ref(v_type_2349_);
                        v_a_2384_ = crate::leanh::lean_ctor_get(v___x_2378_, 0);
                        v_isSharedCheck_2391_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2378_)) as u8;
                        if v_isSharedCheck_2391_ == 0 {
                            v___x_2386_ = v___x_2378_;
                            v_isShared_2387_ = v_isSharedCheck_2391_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2384_);
                            crate::leanh::lean_dec(v___x_2378_);
                            v___x_2386_ = crate::leanh::lean_box(0);
                            v_isShared_2387_ = v_isSharedCheck_2391_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2368_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2366_, 2);
                    crate::leanh::lean_dec_ref(v_semiringInst_2350_);
                    crate::leanh::lean_dec_ref(v_type_2349_);
                    return v___x_2372_;
                }
            }
            1 => {
                if v_isShared_2387_ == 0 {
                    v___x_2389_ = v___x_2386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
                    v___x_2389_ = v_reuseFailAlloc_2390_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_u_2392_: *mut crate::leanh::LeanObject,
    mut v_type_2393_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_2394_: *mut crate::leanh::LeanObject,
    mut v___y_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
    mut v___y_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5(v_u_2392_, v_type_2393_, v_semiringInst_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
    crate::leanh::lean_dec(v___y_2405_);
    crate::leanh::lean_dec_ref(v___y_2404_);
    crate::leanh::lean_dec(v___y_2403_);
    crate::leanh::lean_dec_ref(v___y_2402_);
    crate::leanh::lean_dec(v___y_2401_);
    crate::leanh::lean_dec_ref(v___y_2400_);
    crate::leanh::lean_dec(v___y_2399_);
    crate::leanh::lean_dec_ref(v___y_2398_);
    crate::leanh::lean_dec(v___y_2397_);
    crate::leanh::lean_dec(v___y_2396_);
    crate::leanh::lean_dec(v___y_2395_);
    return v_res_2407_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3___lam__0(
    mut v_a_2408_: *mut crate::leanh::LeanObject,
    mut v_s_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2424_: u8 = 0;
    let mut v_invSet_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2428_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2431_: u8 = 0;
    let mut v_id_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v_unused_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2410_ = crate::leanh::lean_ctor_get(v_s_2409_, 0);
                v_invFn_x3f_2411_ = crate::leanh::lean_ctor_get(v_s_2409_, 1);
                v_semiringId_x3f_2412_ = crate::leanh::lean_ctor_get(v_s_2409_, 2);
                v_commSemiringInst_2413_ = crate::leanh::lean_ctor_get(v_s_2409_, 3);
                v_commRingInst_2414_ = crate::leanh::lean_ctor_get(v_s_2409_, 4);
                v_noZeroDivInst_x3f_2415_ = crate::leanh::lean_ctor_get(v_s_2409_, 5);
                v_fieldInst_x3f_2416_ = crate::leanh::lean_ctor_get(v_s_2409_, 6);
                v_powIdentityInst_x3f_2417_ = crate::leanh::lean_ctor_get(v_s_2409_, 7);
                v_denoteEntries_2418_ = crate::leanh::lean_ctor_get(v_s_2409_, 8);
                v_nextId_2419_ = crate::leanh::lean_ctor_get(v_s_2409_, 9);
                v_steps_2420_ = crate::leanh::lean_ctor_get(v_s_2409_, 10);
                v_queue_2421_ = crate::leanh::lean_ctor_get(v_s_2409_, 11);
                v_basis_2422_ = crate::leanh::lean_ctor_get(v_s_2409_, 12);
                v_diseqs_2423_ = crate::leanh::lean_ctor_get(v_s_2409_, 13);
                v_recheck_2424_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2409_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2425_ = crate::leanh::lean_ctor_get(v_s_2409_, 14);
                v_powIdentityVarCount_2426_ = crate::leanh::lean_ctor_get(v_s_2409_, 15);
                v_numEq0_x3f_2427_ = crate::leanh::lean_ctor_get(v_s_2409_, 16);
                v_numEq0Updated_2428_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2409_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2460_ = (!crate::leanh::lean_is_exclusive(v_s_2409_)) as u8;
                if v_isSharedCheck_2460_ == 0 {
                    v___x_2430_ = v_s_2409_;
                    v_isShared_2431_ = v_isSharedCheck_2460_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2427_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2426_);
                    crate::leanh::lean_inc(v_invSet_2425_);
                    crate::leanh::lean_inc(v_diseqs_2423_);
                    crate::leanh::lean_inc(v_basis_2422_);
                    crate::leanh::lean_inc(v_queue_2421_);
                    crate::leanh::lean_inc(v_steps_2420_);
                    crate::leanh::lean_inc(v_nextId_2419_);
                    crate::leanh::lean_inc(v_denoteEntries_2418_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2417_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2416_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2415_);
                    crate::leanh::lean_inc(v_commRingInst_2414_);
                    crate::leanh::lean_inc(v_commSemiringInst_2413_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2412_);
                    crate::leanh::lean_inc(v_invFn_x3f_2411_);
                    crate::leanh::lean_inc(v_toRing_2410_);
                    crate::leanh::lean_dec(v_s_2409_);
                    v___x_2430_ = crate::leanh::lean_box(0);
                    v_isShared_2431_ = v_isSharedCheck_2460_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2432_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 0);
                v_type_2433_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 1);
                v_u_2434_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 2);
                v_ringInst_2435_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 3);
                v_semiringInst_2436_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 4);
                v_charInst_x3f_2437_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 5);
                v_addFn_x3f_2438_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 6);
                v_mulFn_x3f_2439_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 7);
                v_subFn_x3f_2440_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 8);
                v_negFn_x3f_2441_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 9);
                v_intCastFn_x3f_2442_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 11);
                v_natCastFn_x3f_2443_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 12);
                v_one_x3f_2444_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 13);
                v_vars_2445_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 14);
                v_varMap_2446_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 15);
                v_denote_2447_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 16);
                v_isSharedCheck_2458_ = (!crate::leanh::lean_is_exclusive(v_toRing_2410_)) as u8;
                if v_isSharedCheck_2458_ == 0 {
                    v_unused_2459_ = crate::leanh::lean_ctor_get(v_toRing_2410_, 10);
                    crate::leanh::lean_dec(v_unused_2459_);
                    v___x_2449_ = v_toRing_2410_;
                    v_isShared_2450_ = v_isSharedCheck_2458_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2447_);
                    crate::leanh::lean_inc(v_varMap_2446_);
                    crate::leanh::lean_inc(v_vars_2445_);
                    crate::leanh::lean_inc(v_one_x3f_2444_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2443_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2442_);
                    crate::leanh::lean_inc(v_negFn_x3f_2441_);
                    crate::leanh::lean_inc(v_subFn_x3f_2440_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2439_);
                    crate::leanh::lean_inc(v_addFn_x3f_2438_);
                    crate::leanh::lean_inc(v_charInst_x3f_2437_);
                    crate::leanh::lean_inc(v_semiringInst_2436_);
                    crate::leanh::lean_inc(v_ringInst_2435_);
                    crate::leanh::lean_inc(v_u_2434_);
                    crate::leanh::lean_inc(v_type_2433_);
                    crate::leanh::lean_inc(v_id_2432_);
                    crate::leanh::lean_dec(v_toRing_2410_);
                    v___x_2449_ = crate::leanh::lean_box(0);
                    v_isShared_2450_ = v_isSharedCheck_2458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2451_, 0, v_a_2408_);
                if v_isShared_2450_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2449_, 10, v___x_2451_);
                    v___x_2453_ = v___x_2449_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_id_2432_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_type_2433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_u_2434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_ringInst_2435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_semiringInst_2436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 5, v_charInst_x3f_2437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 6, v_addFn_x3f_2438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 7, v_mulFn_x3f_2439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 8, v_subFn_x3f_2440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 9, v_negFn_x3f_2441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 10, v___x_2451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 11, v_intCastFn_x3f_2442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 12, v_natCastFn_x3f_2443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 13, v_one_x3f_2444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 14, v_vars_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 15, v_varMap_2446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 16, v_denote_2447_);
                    v___x_2453_ = v_reuseFailAlloc_2457_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2431_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2430_, 0, v___x_2453_);
                    v___x_2455_ = v___x_2430_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2456_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_invFn_x3f_2411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_semiringId_x3f_2412_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2456_,
                        3,
                        v_commSemiringInst_2413_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 4, v_commRingInst_2414_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2456_,
                        5,
                        v_noZeroDivInst_x3f_2415_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 6, v_fieldInst_x3f_2416_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2456_,
                        7,
                        v_powIdentityInst_x3f_2417_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 8, v_denoteEntries_2418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 9, v_nextId_2419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 10, v_steps_2420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 11, v_queue_2421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 12, v_basis_2422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 13, v_diseqs_2423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 14, v_invSet_2425_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2456_,
                        15,
                        v_powIdentityVarCount_2426_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 16, v_numEq0_x3f_2427_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2456_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2424_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2456_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2428_,
                    );
                    v___x_2455_ = v_reuseFailAlloc_2456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3(
    mut v___y_2461_: *mut crate::leanh::LeanObject,
    mut v___y_2462_: *mut crate::leanh::LeanObject,
    mut v___y_2463_: *mut crate::leanh::LeanObject,
    mut v___y_2464_: *mut crate::leanh::LeanObject,
    mut v___y_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
    mut v___y_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v_powFn_x3f_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2492_: u8 = 0;
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2496_: u8 = 0;
    let mut v_unused_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2501_: u8 = 0;
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2505_: u8 = 0;
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: u8 = 0;
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v_isSharedCheck_2523_: u8 = 0;
    let mut v_a_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2473_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
                    v___y_2461_,
                    v___y_2462_,
                    v___y_2463_,
                    v___y_2464_,
                    v___y_2465_,
                    v___y_2466_,
                    v___y_2467_,
                    v___y_2468_,
                    v___y_2469_,
                    v___y_2470_,
                    v___y_2471_,
                );
                if crate::leanh::lean_obj_tag(v___x_2473_) == 0 {
                    v_a_2474_ = crate::leanh::lean_ctor_get(v___x_2473_, 0);
                    v_isSharedCheck_2523_ = (!crate::leanh::lean_is_exclusive(v___x_2473_)) as u8;
                    if v_isSharedCheck_2523_ == 0 {
                        v___x_2476_ = v___x_2473_;
                        v_isShared_2477_ = v_isSharedCheck_2523_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2474_);
                        crate::leanh::lean_dec(v___x_2473_);
                        v___x_2476_ = crate::leanh::lean_box(0);
                        v_isShared_2477_ = v_isSharedCheck_2523_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2524_ = crate::leanh::lean_ctor_get(v___x_2473_, 0);
                    v_isSharedCheck_2531_ = (!crate::leanh::lean_is_exclusive(v___x_2473_)) as u8;
                    if v_isSharedCheck_2531_ == 0 {
                        v___x_2526_ = v___x_2473_;
                        v_isShared_2527_ = v_isSharedCheck_2531_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2524_);
                        crate::leanh::lean_dec(v___x_2473_);
                        v___x_2526_ = crate::leanh::lean_box(0);
                        v_isShared_2527_ = v_isSharedCheck_2531_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_powFn_x3f_2478_ = crate::leanh::lean_ctor_get(v_a_2474_, 10);
                if crate::leanh::lean_obj_tag(v_powFn_x3f_2478_) == 1 {
                    crate::leanh::lean_inc_ref(v_powFn_x3f_2478_);
                    crate::leanh::lean_dec(v_a_2474_);
                    v_val_2479_ = crate::leanh::lean_ctor_get(v_powFn_x3f_2478_, 0);
                    crate::leanh::lean_inc(v_val_2479_);
                    crate::leanh::lean_dec_ref_known(v_powFn_x3f_2478_, 1);
                    if v_isShared_2477_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2476_, 0, v_val_2479_);
                        v___x_2481_ = v___x_2476_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_val_2479_);
                        v___x_2481_ = v_reuseFailAlloc_2482_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2476_);
                    v_type_2483_ = crate::leanh::lean_ctor_get(v_a_2474_, 1);
                    crate::leanh::lean_inc_ref(v_type_2483_);
                    v_u_2484_ = crate::leanh::lean_ctor_get(v_a_2474_, 2);
                    crate::leanh::lean_inc(v_u_2484_);
                    v_semiringInst_2485_ = crate::leanh::lean_ctor_get(v_a_2474_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_2485_);
                    crate::leanh::lean_dec(v_a_2474_);
                    v___x_2486_ = l_Lean_Meta_Grind_Arith_CommRing_mkPowFn___at___00Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3_spec__5(v_u_2484_, v_type_2483_, v_semiringInst_2485_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
                    if crate::leanh::lean_obj_tag(v___x_2486_) == 0 {
                        v_a_2487_ = crate::leanh::lean_ctor_get(v___x_2486_, 0);
                        crate::leanh::lean_inc(v_a_2487_);
                        crate::leanh::lean_dec_ref_known(v___x_2486_, 1);
                        v___x_2506_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v___y_2461_,
                            v___y_2462_,
                            v___y_2463_,
                            v___y_2464_,
                            v___y_2465_,
                            v___y_2466_,
                            v___y_2467_,
                            v___y_2468_,
                            v___y_2469_,
                            v___y_2470_,
                            v___y_2471_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2506_) == 0 {
                            v_a_2507_ = crate::leanh::lean_ctor_get(v___x_2506_, 0);
                            crate::leanh::lean_inc(v_a_2507_);
                            crate::leanh::lean_dec_ref_known(v___x_2506_, 1);
                            v_ringId_x3f_2508_ = crate::leanh::lean_ctor_get(v_a_2507_, 1);
                            crate::leanh::lean_inc(v_ringId_x3f_2508_);
                            crate::leanh::lean_dec(v_a_2507_);
                            if crate::leanh::lean_obj_tag(v_ringId_x3f_2508_) == 1 {
                                v_val_2509_ = crate::leanh::lean_ctor_get(v_ringId_x3f_2508_, 0);
                                crate::leanh::lean_inc(v_val_2509_);
                                crate::leanh::lean_dec_ref_known(v_ringId_x3f_2508_, 1);
                                crate::leanh::lean_inc(v_a_2487_);
                                v___f_2510_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3___lam__0 as *mut core::ffi::c_void, 2, 1);
                                crate::leanh::lean_closure_set(v___f_2510_, 0, v_a_2487_);
                                v___x_2511_ = 0;
                                v___x_2512_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_2512_, 0, v_val_2509_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2512_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_2511_,
                                );
                                v___x_2513_ =
                                    l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                        v___f_2510_,
                                        v___x_2512_,
                                        v___y_2462_,
                                    );
                                crate::leanh::lean_dec_ref_known(v___x_2512_, 1);
                                v___y_2489_ = v___x_2513_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_ringId_x3f_2508_);
                                v___x_2514_ =
                                    l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                                        v___y_2468_,
                                        v___y_2469_,
                                        v___y_2470_,
                                        v___y_2471_,
                                    );
                                v___y_2489_ = v___x_2514_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2487_);
                            v_a_2515_ = crate::leanh::lean_ctor_get(v___x_2506_, 0);
                            v_isSharedCheck_2522_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2506_)) as u8;
                            if v_isSharedCheck_2522_ == 0 {
                                v___x_2517_ = v___x_2506_;
                                v_isShared_2518_ = v_isSharedCheck_2522_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2515_);
                                crate::leanh::lean_dec(v___x_2506_);
                                v___x_2517_ = crate::leanh::lean_box(0);
                                v_isShared_2518_ = v_isSharedCheck_2522_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2486_;
                    }
                }
            }
            2 => {
                return v___x_2481_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_2489_) == 0 {
                    v_isSharedCheck_2496_ = (!crate::leanh::lean_is_exclusive(v___y_2489_)) as u8;
                    if v_isSharedCheck_2496_ == 0 {
                        v_unused_2497_ = crate::leanh::lean_ctor_get(v___y_2489_, 0);
                        crate::leanh::lean_dec(v_unused_2497_);
                        v___x_2491_ = v___y_2489_;
                        v_isShared_2492_ = v_isSharedCheck_2496_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2489_);
                        v___x_2491_ = crate::leanh::lean_box(0);
                        v_isShared_2492_ = v_isSharedCheck_2496_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2487_);
                    v_a_2498_ = crate::leanh::lean_ctor_get(v___y_2489_, 0);
                    v_isSharedCheck_2505_ = (!crate::leanh::lean_is_exclusive(v___y_2489_)) as u8;
                    if v_isSharedCheck_2505_ == 0 {
                        v___x_2500_ = v___y_2489_;
                        v_isShared_2501_ = v_isSharedCheck_2505_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2498_);
                        crate::leanh::lean_dec(v___y_2489_);
                        v___x_2500_ = crate::leanh::lean_box(0);
                        v_isShared_2501_ = v_isSharedCheck_2505_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2491_, 0, v_a_2487_);
                    v___x_2494_ = v___x_2491_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2495_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2487_);
                    v___x_2494_ = v_reuseFailAlloc_2495_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2494_;
            }
            6 => {
                if v_isShared_2501_ == 0 {
                    v___x_2503_ = v___x_2500_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2504_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
                    v___x_2503_ = v_reuseFailAlloc_2504_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2503_;
            }
            8 => {
                if v_isShared_2518_ == 0 {
                    v___x_2520_ = v___x_2517_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
                    v___x_2520_ = v_reuseFailAlloc_2521_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2520_;
            }
            10 => {
                if v_isShared_2527_ == 0 {
                    v___x_2529_ = v___x_2526_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
                    v___x_2529_ = v_reuseFailAlloc_2530_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3___boxed(
    mut v___y_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
    mut v___y_2540_: *mut crate::leanh::LeanObject,
    mut v___y_2541_: *mut crate::leanh::LeanObject,
    mut v___y_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2544_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3(v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
    crate::leanh::lean_dec(v___y_2542_);
    crate::leanh::lean_dec_ref(v___y_2541_);
    crate::leanh::lean_dec(v___y_2540_);
    crate::leanh::lean_dec_ref(v___y_2539_);
    crate::leanh::lean_dec(v___y_2538_);
    crate::leanh::lean_dec_ref(v___y_2537_);
    crate::leanh::lean_dec(v___y_2536_);
    crate::leanh::lean_dec_ref(v___y_2535_);
    crate::leanh::lean_dec(v___y_2534_);
    crate::leanh::lean_dec(v___y_2533_);
    crate::leanh::lean_dec(v___y_2532_);
    return v_res_2544_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1(
    mut v_pw_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v_vars_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: u8 = 0;
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut v_a_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2558_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
                    v___y_2546_,
                    v___y_2547_,
                    v___y_2548_,
                    v___y_2549_,
                    v___y_2550_,
                    v___y_2551_,
                    v___y_2552_,
                    v___y_2553_,
                    v___y_2554_,
                    v___y_2555_,
                    v___y_2556_,
                );
                if crate::leanh::lean_obj_tag(v___x_2558_) == 0 {
                    v_a_2559_ = crate::leanh::lean_ctor_get(v___x_2558_, 0);
                    v_isSharedCheck_2589_ = (!crate::leanh::lean_is_exclusive(v___x_2558_)) as u8;
                    if v_isSharedCheck_2589_ == 0 {
                        v___x_2561_ = v___x_2558_;
                        v_isShared_2562_ = v_isSharedCheck_2589_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2559_);
                        crate::leanh::lean_dec(v___x_2558_);
                        v___x_2561_ = crate::leanh::lean_box(0);
                        v_isShared_2562_ = v_isSharedCheck_2589_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_pw_2545_);
                    v_a_2590_ = crate::leanh::lean_ctor_get(v___x_2558_, 0);
                    v_isSharedCheck_2597_ = (!crate::leanh::lean_is_exclusive(v___x_2558_)) as u8;
                    if v_isSharedCheck_2597_ == 0 {
                        v___x_2592_ = v___x_2558_;
                        v_isShared_2593_ = v_isSharedCheck_2597_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2590_);
                        crate::leanh::lean_dec(v___x_2558_);
                        v___x_2592_ = crate::leanh::lean_box(0);
                        v_isShared_2593_ = v_isSharedCheck_2597_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_vars_2563_ = crate::leanh::lean_ctor_get(v_a_2559_, 14);
                crate::leanh::lean_inc_ref(v_vars_2563_);
                crate::leanh::lean_dec(v_a_2559_);
                v_x_2564_ = crate::leanh::lean_ctor_get(v_pw_2545_, 0);
                crate::leanh::lean_inc(v_x_2564_);
                v_k_2565_ = crate::leanh::lean_ctor_get(v_pw_2545_, 1);
                crate::leanh::lean_inc(v_k_2565_);
                crate::leanh::lean_dec_ref(v_pw_2545_);
                v_size_2584_ = crate::leanh::lean_ctor_get(v_vars_2563_, 2);
                v___x_2585_ = l_Lean_instInhabitedExpr;
                v___x_2586_ = lean_nat_dec_lt(v_x_2564_, v_size_2584_);
                if v___x_2586_ == 0 {
                    crate::leanh::lean_dec(v_x_2564_);
                    crate::leanh::lean_dec_ref(v_vars_2563_);
                    v___x_2587_ = l_outOfBounds___redArg(v___x_2585_);
                    v___y_2567_ = v___x_2587_;
                    state = 2;
                    continue;
                } else {
                    v___x_2588_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_2585_,
                        v_vars_2563_,
                        v_x_2564_,
                    );
                    crate::leanh::lean_dec(v_x_2564_);
                    crate::leanh::lean_dec_ref(v_vars_2563_);
                    v___y_2567_ = v___x_2588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2568_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2569_ = lean_nat_dec_eq(v_k_2565_, v___x_2568_);
                if v___x_2569_ == 0 {
                    crate::leanh::lean_del_object(v___x_2561_);
                    v___x_2570_ = l_Lean_Meta_Grind_Arith_CommRing_getPowFn___at___00Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1_spec__3(v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
                    if crate::leanh::lean_obj_tag(v___x_2570_) == 0 {
                        v_a_2571_ = crate::leanh::lean_ctor_get(v___x_2570_, 0);
                        v_isSharedCheck_2580_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2570_)) as u8;
                        if v_isSharedCheck_2580_ == 0 {
                            v___x_2573_ = v___x_2570_;
                            v_isShared_2574_ = v_isSharedCheck_2580_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2571_);
                            crate::leanh::lean_dec(v___x_2570_);
                            v___x_2573_ = crate::leanh::lean_box(0);
                            v_isShared_2574_ = v_isSharedCheck_2580_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_2567_);
                        crate::leanh::lean_dec(v_k_2565_);
                        return v___x_2570_;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_2565_);
                    if v_isShared_2562_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2561_, 0, v___y_2567_);
                        v___x_2582_ = v___x_2561_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___y_2567_);
                        v___x_2582_ = v_reuseFailAlloc_2583_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2575_ = l_Lean_mkNatLit(v_k_2565_);
                v___x_2576_ = l_Lean_mkAppB(v_a_2571_, v___y_2567_, v___x_2575_);
                if v_isShared_2574_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2573_, 0, v___x_2576_);
                    v___x_2578_ = v___x_2573_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
                    v___x_2578_ = v_reuseFailAlloc_2579_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2578_;
            }
            5 => {
                return v___x_2582_;
            }
            6 => {
                if v_isShared_2593_ == 0 {
                    v___x_2595_ = v___x_2592_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2596_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
                    v___x_2595_ = v_reuseFailAlloc_2596_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1___boxed(
    mut v_pw_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2611_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1(v_pw_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_);
    crate::leanh::lean_dec(v___y_2609_);
    crate::leanh::lean_dec_ref(v___y_2608_);
    crate::leanh::lean_dec(v___y_2607_);
    crate::leanh::lean_dec_ref(v___y_2606_);
    crate::leanh::lean_dec(v___y_2605_);
    crate::leanh::lean_dec_ref(v___y_2604_);
    crate::leanh::lean_dec(v___y_2603_);
    crate::leanh::lean_dec_ref(v___y_2602_);
    crate::leanh::lean_dec(v___y_2601_);
    crate::leanh::lean_dec(v___y_2600_);
    crate::leanh::lean_dec(v___y_2599_);
    return v_res_2611_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___lam__0(
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_s_2613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2628_: u8 = 0;
    let mut v_invSet_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2632_: u8 = 0;
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2635_: u8 = 0;
    let mut v_id_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_negFn_x3f_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_unused_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2614_ = crate::leanh::lean_ctor_get(v_s_2613_, 0);
                v_invFn_x3f_2615_ = crate::leanh::lean_ctor_get(v_s_2613_, 1);
                v_semiringId_x3f_2616_ = crate::leanh::lean_ctor_get(v_s_2613_, 2);
                v_commSemiringInst_2617_ = crate::leanh::lean_ctor_get(v_s_2613_, 3);
                v_commRingInst_2618_ = crate::leanh::lean_ctor_get(v_s_2613_, 4);
                v_noZeroDivInst_x3f_2619_ = crate::leanh::lean_ctor_get(v_s_2613_, 5);
                v_fieldInst_x3f_2620_ = crate::leanh::lean_ctor_get(v_s_2613_, 6);
                v_powIdentityInst_x3f_2621_ = crate::leanh::lean_ctor_get(v_s_2613_, 7);
                v_denoteEntries_2622_ = crate::leanh::lean_ctor_get(v_s_2613_, 8);
                v_nextId_2623_ = crate::leanh::lean_ctor_get(v_s_2613_, 9);
                v_steps_2624_ = crate::leanh::lean_ctor_get(v_s_2613_, 10);
                v_queue_2625_ = crate::leanh::lean_ctor_get(v_s_2613_, 11);
                v_basis_2626_ = crate::leanh::lean_ctor_get(v_s_2613_, 12);
                v_diseqs_2627_ = crate::leanh::lean_ctor_get(v_s_2613_, 13);
                v_recheck_2628_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2613_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2629_ = crate::leanh::lean_ctor_get(v_s_2613_, 14);
                v_powIdentityVarCount_2630_ = crate::leanh::lean_ctor_get(v_s_2613_, 15);
                v_numEq0_x3f_2631_ = crate::leanh::lean_ctor_get(v_s_2613_, 16);
                v_numEq0Updated_2632_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2613_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2664_ = (!crate::leanh::lean_is_exclusive(v_s_2613_)) as u8;
                if v_isSharedCheck_2664_ == 0 {
                    v___x_2634_ = v_s_2613_;
                    v_isShared_2635_ = v_isSharedCheck_2664_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2631_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2630_);
                    crate::leanh::lean_inc(v_invSet_2629_);
                    crate::leanh::lean_inc(v_diseqs_2627_);
                    crate::leanh::lean_inc(v_basis_2626_);
                    crate::leanh::lean_inc(v_queue_2625_);
                    crate::leanh::lean_inc(v_steps_2624_);
                    crate::leanh::lean_inc(v_nextId_2623_);
                    crate::leanh::lean_inc(v_denoteEntries_2622_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2621_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2620_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2619_);
                    crate::leanh::lean_inc(v_commRingInst_2618_);
                    crate::leanh::lean_inc(v_commSemiringInst_2617_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2616_);
                    crate::leanh::lean_inc(v_invFn_x3f_2615_);
                    crate::leanh::lean_inc(v_toRing_2614_);
                    crate::leanh::lean_dec(v_s_2613_);
                    v___x_2634_ = crate::leanh::lean_box(0);
                    v_isShared_2635_ = v_isSharedCheck_2664_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2636_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 0);
                v_type_2637_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 1);
                v_u_2638_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 2);
                v_ringInst_2639_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 3);
                v_semiringInst_2640_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 4);
                v_charInst_x3f_2641_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 5);
                v_addFn_x3f_2642_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 6);
                v_subFn_x3f_2643_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 8);
                v_negFn_x3f_2644_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 9);
                v_powFn_x3f_2645_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 10);
                v_intCastFn_x3f_2646_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 11);
                v_natCastFn_x3f_2647_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 12);
                v_one_x3f_2648_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 13);
                v_vars_2649_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 14);
                v_varMap_2650_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 15);
                v_denote_2651_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 16);
                v_isSharedCheck_2662_ = (!crate::leanh::lean_is_exclusive(v_toRing_2614_)) as u8;
                if v_isSharedCheck_2662_ == 0 {
                    v_unused_2663_ = crate::leanh::lean_ctor_get(v_toRing_2614_, 7);
                    crate::leanh::lean_dec(v_unused_2663_);
                    v___x_2653_ = v_toRing_2614_;
                    v_isShared_2654_ = v_isSharedCheck_2662_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2651_);
                    crate::leanh::lean_inc(v_varMap_2650_);
                    crate::leanh::lean_inc(v_vars_2649_);
                    crate::leanh::lean_inc(v_one_x3f_2648_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2647_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2646_);
                    crate::leanh::lean_inc(v_powFn_x3f_2645_);
                    crate::leanh::lean_inc(v_negFn_x3f_2644_);
                    crate::leanh::lean_inc(v_subFn_x3f_2643_);
                    crate::leanh::lean_inc(v_addFn_x3f_2642_);
                    crate::leanh::lean_inc(v_charInst_x3f_2641_);
                    crate::leanh::lean_inc(v_semiringInst_2640_);
                    crate::leanh::lean_inc(v_ringInst_2639_);
                    crate::leanh::lean_inc(v_u_2638_);
                    crate::leanh::lean_inc(v_type_2637_);
                    crate::leanh::lean_inc(v_id_2636_);
                    crate::leanh::lean_dec(v_toRing_2614_);
                    v___x_2653_ = crate::leanh::lean_box(0);
                    v_isShared_2654_ = v_isSharedCheck_2662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2655_, 0, v_a_2612_);
                if v_isShared_2654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2653_, 7, v___x_2655_);
                    v___x_2657_ = v___x_2653_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_id_2636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_type_2637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 2, v_u_2638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 3, v_ringInst_2639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 4, v_semiringInst_2640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 5, v_charInst_x3f_2641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 6, v_addFn_x3f_2642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 7, v___x_2655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 8, v_subFn_x3f_2643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 9, v_negFn_x3f_2644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 10, v_powFn_x3f_2645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 11, v_intCastFn_x3f_2646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 12, v_natCastFn_x3f_2647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 13, v_one_x3f_2648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 14, v_vars_2649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 15, v_varMap_2650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 16, v_denote_2651_);
                    v___x_2657_ = v_reuseFailAlloc_2661_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2634_, 0, v___x_2657_);
                    v___x_2659_ = v___x_2634_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 1, v_invFn_x3f_2615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 2, v_semiringId_x3f_2616_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2660_,
                        3,
                        v_commSemiringInst_2617_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 4, v_commRingInst_2618_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2660_,
                        5,
                        v_noZeroDivInst_x3f_2619_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 6, v_fieldInst_x3f_2620_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2660_,
                        7,
                        v_powIdentityInst_x3f_2621_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 8, v_denoteEntries_2622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 9, v_nextId_2623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 10, v_steps_2624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 11, v_queue_2625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 12, v_basis_2626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 13, v_diseqs_2627_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 14, v_invSet_2629_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2660_,
                        15,
                        v_powIdentityVarCount_2630_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 16, v_numEq0_x3f_2631_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2660_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2628_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2660_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2632_,
                    );
                    v___x_2659_ = v_reuseFailAlloc_2660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5_spec__8(
    mut v_type_2665_: *mut crate::leanh::LeanObject,
    mut v_u_2666_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_2667_: *mut crate::leanh::LeanObject,
    mut v_declName_2668_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_2669_: *mut crate::leanh::LeanObject,
    mut v___y_2670_: *mut crate::leanh::LeanObject,
    mut v___y_2671_: *mut crate::leanh::LeanObject,
    mut v___y_2672_: *mut crate::leanh::LeanObject,
    mut v___y_2673_: *mut crate::leanh::LeanObject,
    mut v___y_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
    mut v___y_2678_: *mut crate::leanh::LeanObject,
    mut v___y_2679_: *mut crate::leanh::LeanObject,
    mut v___y_2680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2699_: u8 = 0;
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2682_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_n(v_u_2666_, 2);
                v___x_2683_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2683_, 0, v_u_2666_);
                crate::leanh::lean_ctor_set(v___x_2683_, 1, v___x_2682_);
                v___x_2684_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2684_, 0, v_u_2666_);
                crate::leanh::lean_ctor_set(v___x_2684_, 1, v___x_2683_);
                v___x_2685_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2685_, 0, v_u_2666_);
                crate::leanh::lean_ctor_set(v___x_2685_, 1, v___x_2684_);
                crate::leanh::lean_inc_ref(v___x_2685_);
                v___x_2686_ = l_Lean_mkConst(v_instDeclName_2667_, v___x_2685_);
                crate::leanh::lean_inc_ref_n(v_type_2665_, 3);
                v___x_2687_ = l_Lean_mkApp3(v___x_2686_, v_type_2665_, v_type_2665_, v_type_2665_);
                v___x_2688_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5(v___x_2687_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
                if crate::leanh::lean_obj_tag(v___x_2688_) == 0 {
                    v_a_2689_ = crate::leanh::lean_ctor_get(v___x_2688_, 0);
                    crate::leanh::lean_inc_n(v_a_2689_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2688_, 1);
                    crate::leanh::lean_inc(v_declName_2668_);
                    v___x_2690_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_2668_,
                        v_a_2689_,
                        v_expectedInst_2669_,
                        v___y_2677_,
                        v___y_2678_,
                        v___y_2679_,
                        v___y_2680_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2690_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2690_, 1);
                        v___x_2691_ = l_Lean_mkConst(v_declName_2668_, v___x_2685_);
                        crate::leanh::lean_inc_ref_n(v_type_2665_, 2);
                        v___x_2692_ = l_Lean_mkApp4(
                            v___x_2691_,
                            v_type_2665_,
                            v_type_2665_,
                            v_type_2665_,
                            v_a_2689_,
                        );
                        v___x_2693_ = l_Lean_Meta_Sym_canon(
                            v___x_2692_,
                            v___y_2675_,
                            v___y_2676_,
                            v___y_2677_,
                            v___y_2678_,
                            v___y_2679_,
                            v___y_2680_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2693_) == 0 {
                            v_a_2694_ = crate::leanh::lean_ctor_get(v___x_2693_, 0);
                            crate::leanh::lean_inc(v_a_2694_);
                            crate::leanh::lean_dec_ref_known(v___x_2693_, 1);
                            v___x_2695_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_2694_, v___y_2676_);
                            return v___x_2695_;
                        } else {
                            return v___x_2693_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2689_);
                        crate::leanh::lean_dec_ref_known(v___x_2685_, 2);
                        crate::leanh::lean_dec(v_declName_2668_);
                        crate::leanh::lean_dec_ref(v_type_2665_);
                        v_a_2696_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                        v_isSharedCheck_2703_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2690_)) as u8;
                        if v_isSharedCheck_2703_ == 0 {
                            v___x_2698_ = v___x_2690_;
                            v_isShared_2699_ = v_isSharedCheck_2703_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2696_);
                            crate::leanh::lean_dec(v___x_2690_);
                            v___x_2698_ = crate::leanh::lean_box(0);
                            v_isShared_2699_ = v_isSharedCheck_2703_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2685_, 2);
                    crate::leanh::lean_dec_ref(v_expectedInst_2669_);
                    crate::leanh::lean_dec(v_declName_2668_);
                    crate::leanh::lean_dec_ref(v_type_2665_);
                    return v___x_2688_;
                }
            }
            1 => {
                if v_isShared_2699_ == 0 {
                    v___x_2701_ = v___x_2698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
                    v___x_2701_ = v_reuseFailAlloc_2702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5_spec__8___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2704_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_u_2705_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_2706_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_declName_2707_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_2708_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_2709_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2710_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2711_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2712_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2713_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2714_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2715_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2716_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2717_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2718_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2719_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2720_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5_spec__8(v_type_2704_, v_u_2705_, v_instDeclName_2706_, v_declName_2707_, v_expectedInst_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
    crate::leanh::lean_dec(v___y_2719_);
    crate::leanh::lean_dec_ref(v___y_2718_);
    crate::leanh::lean_dec(v___y_2717_);
    crate::leanh::lean_dec_ref(v___y_2716_);
    crate::leanh::lean_dec(v___y_2715_);
    crate::leanh::lean_dec_ref(v___y_2714_);
    crate::leanh::lean_dec(v___y_2713_);
    crate::leanh::lean_dec_ref(v___y_2712_);
    crate::leanh::lean_dec(v___y_2711_);
    crate::leanh::lean_dec(v___y_2710_);
    crate::leanh::lean_dec(v___y_2709_);
    return v_res_2721_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5(
    mut v___y_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___y_2742_: *mut crate::leanh::LeanObject,
    mut v___y_2743_: *mut crate::leanh::LeanObject,
    mut v___y_2744_: *mut crate::leanh::LeanObject,
    mut v___y_2745_: *mut crate::leanh::LeanObject,
    mut v___y_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
    mut v___y_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v_mulFn_x3f_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2783_: u8 = 0;
    let mut v_unused_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2792_: u8 = 0;
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: u8 = 0;
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2805_: u8 = 0;
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2809_: u8 = 0;
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v_a_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2814_: u8 = 0;
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2750_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
                    v___y_2738_,
                    v___y_2739_,
                    v___y_2740_,
                    v___y_2741_,
                    v___y_2742_,
                    v___y_2743_,
                    v___y_2744_,
                    v___y_2745_,
                    v___y_2746_,
                    v___y_2747_,
                    v___y_2748_,
                );
                if crate::leanh::lean_obj_tag(v___x_2750_) == 0 {
                    v_a_2751_ = crate::leanh::lean_ctor_get(v___x_2750_, 0);
                    v_isSharedCheck_2810_ = (!crate::leanh::lean_is_exclusive(v___x_2750_)) as u8;
                    if v_isSharedCheck_2810_ == 0 {
                        v___x_2753_ = v___x_2750_;
                        v_isShared_2754_ = v_isSharedCheck_2810_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2751_);
                        crate::leanh::lean_dec(v___x_2750_);
                        v___x_2753_ = crate::leanh::lean_box(0);
                        v_isShared_2754_ = v_isSharedCheck_2810_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2811_ = crate::leanh::lean_ctor_get(v___x_2750_, 0);
                    v_isSharedCheck_2818_ = (!crate::leanh::lean_is_exclusive(v___x_2750_)) as u8;
                    if v_isSharedCheck_2818_ == 0 {
                        v___x_2813_ = v___x_2750_;
                        v_isShared_2814_ = v_isSharedCheck_2818_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2811_);
                        crate::leanh::lean_dec(v___x_2750_);
                        v___x_2813_ = crate::leanh::lean_box(0);
                        v_isShared_2814_ = v_isSharedCheck_2818_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_mulFn_x3f_2755_ = crate::leanh::lean_ctor_get(v_a_2751_, 7);
                if crate::leanh::lean_obj_tag(v_mulFn_x3f_2755_) == 1 {
                    crate::leanh::lean_inc_ref(v_mulFn_x3f_2755_);
                    crate::leanh::lean_dec(v_a_2751_);
                    v_val_2756_ = crate::leanh::lean_ctor_get(v_mulFn_x3f_2755_, 0);
                    crate::leanh::lean_inc(v_val_2756_);
                    crate::leanh::lean_dec_ref_known(v_mulFn_x3f_2755_, 1);
                    if v_isShared_2754_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2753_, 0, v_val_2756_);
                        v___x_2758_ = v___x_2753_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_val_2756_);
                        v___x_2758_ = v_reuseFailAlloc_2759_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2753_);
                    v_type_2760_ = crate::leanh::lean_ctor_get(v_a_2751_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_2760_, 3);
                    v_u_2761_ = crate::leanh::lean_ctor_get(v_a_2751_, 2);
                    crate::leanh::lean_inc_n(v_u_2761_, 2);
                    v_semiringInst_2762_ = crate::leanh::lean_ctor_get(v_a_2751_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_2762_);
                    crate::leanh::lean_dec(v_a_2751_);
                    v___x_2763_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__1;
                    v___x_2764_ = crate::leanh::lean_box(0);
                    v___x_2765_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2765_, 0, v_u_2761_);
                    crate::leanh::lean_ctor_set(v___x_2765_, 1, v___x_2764_);
                    crate::leanh::lean_inc_ref(v___x_2765_);
                    v___x_2766_ = l_Lean_mkConst(v___x_2763_, v___x_2765_);
                    v___x_2767_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__3;
                    v___x_2768_ = l_Lean_mkConst(v___x_2767_, v___x_2765_);
                    v___x_2769_ = l_Lean_mkAppB(v___x_2768_, v_type_2760_, v_semiringInst_2762_);
                    v_expectedInst_2770_ = l_Lean_mkAppB(v___x_2766_, v_type_2760_, v___x_2769_);
                    v___x_2771_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__5;
                    v___x_2772_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___closed__7;
                    v___x_2773_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5_spec__8(v_type_2760_, v_u_2761_, v___x_2771_, v___x_2772_, v_expectedInst_2770_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
                    if crate::leanh::lean_obj_tag(v___x_2773_) == 0 {
                        v_a_2774_ = crate::leanh::lean_ctor_get(v___x_2773_, 0);
                        crate::leanh::lean_inc(v_a_2774_);
                        crate::leanh::lean_dec_ref_known(v___x_2773_, 1);
                        v___x_2793_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v___y_2738_,
                            v___y_2739_,
                            v___y_2740_,
                            v___y_2741_,
                            v___y_2742_,
                            v___y_2743_,
                            v___y_2744_,
                            v___y_2745_,
                            v___y_2746_,
                            v___y_2747_,
                            v___y_2748_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2793_) == 0 {
                            v_a_2794_ = crate::leanh::lean_ctor_get(v___x_2793_, 0);
                            crate::leanh::lean_inc(v_a_2794_);
                            crate::leanh::lean_dec_ref_known(v___x_2793_, 1);
                            v_ringId_x3f_2795_ = crate::leanh::lean_ctor_get(v_a_2794_, 1);
                            crate::leanh::lean_inc(v_ringId_x3f_2795_);
                            crate::leanh::lean_dec(v_a_2794_);
                            if crate::leanh::lean_obj_tag(v_ringId_x3f_2795_) == 1 {
                                v_val_2796_ = crate::leanh::lean_ctor_get(v_ringId_x3f_2795_, 0);
                                crate::leanh::lean_inc(v_val_2796_);
                                crate::leanh::lean_dec_ref_known(v_ringId_x3f_2795_, 1);
                                crate::leanh::lean_inc(v_a_2774_);
                                v___f_2797_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___lam__0 as *mut core::ffi::c_void, 2, 1);
                                crate::leanh::lean_closure_set(v___f_2797_, 0, v_a_2774_);
                                v___x_2798_ = 0;
                                v___x_2799_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_2799_, 0, v_val_2796_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_2799_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_2798_,
                                );
                                v___x_2800_ =
                                    l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                        v___f_2797_,
                                        v___x_2799_,
                                        v___y_2739_,
                                    );
                                crate::leanh::lean_dec_ref_known(v___x_2799_, 1);
                                v___y_2776_ = v___x_2800_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_ringId_x3f_2795_);
                                v___x_2801_ =
                                    l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                                        v___y_2745_,
                                        v___y_2746_,
                                        v___y_2747_,
                                        v___y_2748_,
                                    );
                                v___y_2776_ = v___x_2801_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2774_);
                            v_a_2802_ = crate::leanh::lean_ctor_get(v___x_2793_, 0);
                            v_isSharedCheck_2809_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2793_)) as u8;
                            if v_isSharedCheck_2809_ == 0 {
                                v___x_2804_ = v___x_2793_;
                                v_isShared_2805_ = v_isSharedCheck_2809_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2802_);
                                crate::leanh::lean_dec(v___x_2793_);
                                v___x_2804_ = crate::leanh::lean_box(0);
                                v_isShared_2805_ = v_isSharedCheck_2809_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2773_;
                    }
                }
            }
            2 => {
                return v___x_2758_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_2776_) == 0 {
                    v_isSharedCheck_2783_ = (!crate::leanh::lean_is_exclusive(v___y_2776_)) as u8;
                    if v_isSharedCheck_2783_ == 0 {
                        v_unused_2784_ = crate::leanh::lean_ctor_get(v___y_2776_, 0);
                        crate::leanh::lean_dec(v_unused_2784_);
                        v___x_2778_ = v___y_2776_;
                        v_isShared_2779_ = v_isSharedCheck_2783_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2776_);
                        v___x_2778_ = crate::leanh::lean_box(0);
                        v_isShared_2779_ = v_isSharedCheck_2783_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2774_);
                    v_a_2785_ = crate::leanh::lean_ctor_get(v___y_2776_, 0);
                    v_isSharedCheck_2792_ = (!crate::leanh::lean_is_exclusive(v___y_2776_)) as u8;
                    if v_isSharedCheck_2792_ == 0 {
                        v___x_2787_ = v___y_2776_;
                        v_isShared_2788_ = v_isSharedCheck_2792_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2785_);
                        crate::leanh::lean_dec(v___y_2776_);
                        v___x_2787_ = crate::leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2792_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2778_, 0, v_a_2774_);
                    v___x_2781_ = v___x_2778_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2774_);
                    v___x_2781_ = v_reuseFailAlloc_2782_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2781_;
            }
            6 => {
                if v_isShared_2788_ == 0 {
                    v___x_2790_ = v___x_2787_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
                    v___x_2790_ = v_reuseFailAlloc_2791_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2790_;
            }
            8 => {
                if v_isShared_2805_ == 0 {
                    v___x_2807_ = v___x_2804_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
                    v___x_2807_ = v_reuseFailAlloc_2808_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2807_;
            }
            10 => {
                if v_isShared_2814_ == 0 {
                    v___x_2816_ = v___x_2813_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
                    v___x_2816_ = v_reuseFailAlloc_2817_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5___boxed(
    mut v___y_2819_: *mut crate::leanh::LeanObject,
    mut v___y_2820_: *mut crate::leanh::LeanObject,
    mut v___y_2821_: *mut crate::leanh::LeanObject,
    mut v___y_2822_: *mut crate::leanh::LeanObject,
    mut v___y_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
    mut v___y_2828_: *mut crate::leanh::LeanObject,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
    mut v___y_2830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2831_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5(v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
    crate::leanh::lean_dec(v___y_2829_);
    crate::leanh::lean_dec_ref(v___y_2828_);
    crate::leanh::lean_dec(v___y_2827_);
    crate::leanh::lean_dec_ref(v___y_2826_);
    crate::leanh::lean_dec(v___y_2825_);
    crate::leanh::lean_dec_ref(v___y_2824_);
    crate::leanh::lean_dec(v___y_2823_);
    crate::leanh::lean_dec_ref(v___y_2822_);
    crate::leanh::lean_dec(v___y_2821_);
    crate::leanh::lean_dec(v___y_2820_);
    crate::leanh::lean_dec(v___y_2819_);
    return v_res_2831_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2(
    mut v_m_2832_: *mut crate::leanh::LeanObject,
    mut v_acc_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
    mut v___y_2838_: *mut crate::leanh::LeanObject,
    mut v___y_2839_: *mut crate::leanh::LeanObject,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
    mut v___y_2841_: *mut crate::leanh::LeanObject,
    mut v___y_2842_: *mut crate::leanh::LeanObject,
    mut v___y_2843_: *mut crate::leanh::LeanObject,
    mut v___y_2844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_2832_) == 0 {
                    v___x_2846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2846_, 0, v_acc_2833_);
                    return v___x_2846_;
                } else {
                    v_p_2847_ = crate::leanh::lean_ctor_get(v_m_2832_, 0);
                    crate::leanh::lean_inc_ref(v_p_2847_);
                    v_m_2848_ = crate::leanh::lean_ctor_get(v_m_2832_, 1);
                    crate::leanh::lean_inc(v_m_2848_);
                    crate::leanh::lean_dec_ref_known(v_m_2832_, 2);
                    v___x_2849_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2_spec__5(v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
                    if crate::leanh::lean_obj_tag(v___x_2849_) == 0 {
                        v_a_2850_ = crate::leanh::lean_ctor_get(v___x_2849_, 0);
                        crate::leanh::lean_inc(v_a_2850_);
                        crate::leanh::lean_dec_ref_known(v___x_2849_, 1);
                        v___x_2851_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1(v_p_2847_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
                        if crate::leanh::lean_obj_tag(v___x_2851_) == 0 {
                            v_a_2852_ = crate::leanh::lean_ctor_get(v___x_2851_, 0);
                            crate::leanh::lean_inc(v_a_2852_);
                            crate::leanh::lean_dec_ref_known(v___x_2851_, 1);
                            v___x_2853_ = l_Lean_mkAppB(v_a_2850_, v_acc_2833_, v_a_2852_);
                            v_m_2832_ = v_m_2848_;
                            v_acc_2833_ = v___x_2853_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2850_);
                            crate::leanh::lean_dec(v_m_2848_);
                            crate::leanh::lean_dec_ref(v_acc_2833_);
                            return v___x_2851_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_m_2848_);
                        crate::leanh::lean_dec_ref(v_p_2847_);
                        crate::leanh::lean_dec_ref(v_acc_2833_);
                        return v___x_2849_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2___boxed(
    mut v_m_2855_: *mut crate::leanh::LeanObject,
    mut v_acc_2856_: *mut crate::leanh::LeanObject,
    mut v___y_2857_: *mut crate::leanh::LeanObject,
    mut v___y_2858_: *mut crate::leanh::LeanObject,
    mut v___y_2859_: *mut crate::leanh::LeanObject,
    mut v___y_2860_: *mut crate::leanh::LeanObject,
    mut v___y_2861_: *mut crate::leanh::LeanObject,
    mut v___y_2862_: *mut crate::leanh::LeanObject,
    mut v___y_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
    mut v___y_2868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2869_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2(v_m_2855_, v_acc_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_);
    crate::leanh::lean_dec(v___y_2867_);
    crate::leanh::lean_dec_ref(v___y_2866_);
    crate::leanh::lean_dec(v___y_2865_);
    crate::leanh::lean_dec_ref(v___y_2864_);
    crate::leanh::lean_dec(v___y_2863_);
    crate::leanh::lean_dec_ref(v___y_2862_);
    crate::leanh::lean_dec(v___y_2861_);
    crate::leanh::lean_dec_ref(v___y_2860_);
    crate::leanh::lean_dec(v___y_2859_);
    crate::leanh::lean_dec(v___y_2858_);
    crate::leanh::lean_dec(v___y_2857_);
    return v_res_2869_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___lam__0(
    mut v_a_2870_: *mut crate::leanh::LeanObject,
    mut v_s_2871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toRing_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringId_x3f_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityInst_x3f_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recheck_2886_: u8 = 0;
    let mut v_invSet_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powIdentityVarCount_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0_x3f_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numEq0Updated_2890_: u8 = 0;
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v_id_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_x3f_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mulFn_x3f_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subFn_x3f_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_powFn_x3f_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intCastFn_x3f_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCastFn_x3f_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut v_unused_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toRing_2872_ = crate::leanh::lean_ctor_get(v_s_2871_, 0);
                v_invFn_x3f_2873_ = crate::leanh::lean_ctor_get(v_s_2871_, 1);
                v_semiringId_x3f_2874_ = crate::leanh::lean_ctor_get(v_s_2871_, 2);
                v_commSemiringInst_2875_ = crate::leanh::lean_ctor_get(v_s_2871_, 3);
                v_commRingInst_2876_ = crate::leanh::lean_ctor_get(v_s_2871_, 4);
                v_noZeroDivInst_x3f_2877_ = crate::leanh::lean_ctor_get(v_s_2871_, 5);
                v_fieldInst_x3f_2878_ = crate::leanh::lean_ctor_get(v_s_2871_, 6);
                v_powIdentityInst_x3f_2879_ = crate::leanh::lean_ctor_get(v_s_2871_, 7);
                v_denoteEntries_2880_ = crate::leanh::lean_ctor_get(v_s_2871_, 8);
                v_nextId_2881_ = crate::leanh::lean_ctor_get(v_s_2871_, 9);
                v_steps_2882_ = crate::leanh::lean_ctor_get(v_s_2871_, 10);
                v_queue_2883_ = crate::leanh::lean_ctor_get(v_s_2871_, 11);
                v_basis_2884_ = crate::leanh::lean_ctor_get(v_s_2871_, 12);
                v_diseqs_2885_ = crate::leanh::lean_ctor_get(v_s_2871_, 13);
                v_recheck_2886_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_invSet_2887_ = crate::leanh::lean_ctor_get(v_s_2871_, 14);
                v_powIdentityVarCount_2888_ = crate::leanh::lean_ctor_get(v_s_2871_, 15);
                v_numEq0_x3f_2889_ = crate::leanh::lean_ctor_get(v_s_2871_, 16);
                v_numEq0Updated_2890_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_2871_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                );
                v_isSharedCheck_2922_ = (!crate::leanh::lean_is_exclusive(v_s_2871_)) as u8;
                if v_isSharedCheck_2922_ == 0 {
                    v___x_2892_ = v_s_2871_;
                    v_isShared_2893_ = v_isSharedCheck_2922_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numEq0_x3f_2889_);
                    crate::leanh::lean_inc(v_powIdentityVarCount_2888_);
                    crate::leanh::lean_inc(v_invSet_2887_);
                    crate::leanh::lean_inc(v_diseqs_2885_);
                    crate::leanh::lean_inc(v_basis_2884_);
                    crate::leanh::lean_inc(v_queue_2883_);
                    crate::leanh::lean_inc(v_steps_2882_);
                    crate::leanh::lean_inc(v_nextId_2881_);
                    crate::leanh::lean_inc(v_denoteEntries_2880_);
                    crate::leanh::lean_inc(v_powIdentityInst_x3f_2879_);
                    crate::leanh::lean_inc(v_fieldInst_x3f_2878_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2877_);
                    crate::leanh::lean_inc(v_commRingInst_2876_);
                    crate::leanh::lean_inc(v_commSemiringInst_2875_);
                    crate::leanh::lean_inc(v_semiringId_x3f_2874_);
                    crate::leanh::lean_inc(v_invFn_x3f_2873_);
                    crate::leanh::lean_inc(v_toRing_2872_);
                    crate::leanh::lean_dec(v_s_2871_);
                    v___x_2892_ = crate::leanh::lean_box(0);
                    v_isShared_2893_ = v_isSharedCheck_2922_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_id_2894_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 0);
                v_type_2895_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 1);
                v_u_2896_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 2);
                v_ringInst_2897_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 3);
                v_semiringInst_2898_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 4);
                v_charInst_x3f_2899_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 5);
                v_addFn_x3f_2900_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 6);
                v_mulFn_x3f_2901_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 7);
                v_subFn_x3f_2902_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 8);
                v_powFn_x3f_2903_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 10);
                v_intCastFn_x3f_2904_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 11);
                v_natCastFn_x3f_2905_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 12);
                v_one_x3f_2906_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 13);
                v_vars_2907_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 14);
                v_varMap_2908_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 15);
                v_denote_2909_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 16);
                v_isSharedCheck_2920_ = (!crate::leanh::lean_is_exclusive(v_toRing_2872_)) as u8;
                if v_isSharedCheck_2920_ == 0 {
                    v_unused_2921_ = crate::leanh::lean_ctor_get(v_toRing_2872_, 9);
                    crate::leanh::lean_dec(v_unused_2921_);
                    v___x_2911_ = v_toRing_2872_;
                    v_isShared_2912_ = v_isSharedCheck_2920_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_denote_2909_);
                    crate::leanh::lean_inc(v_varMap_2908_);
                    crate::leanh::lean_inc(v_vars_2907_);
                    crate::leanh::lean_inc(v_one_x3f_2906_);
                    crate::leanh::lean_inc(v_natCastFn_x3f_2905_);
                    crate::leanh::lean_inc(v_intCastFn_x3f_2904_);
                    crate::leanh::lean_inc(v_powFn_x3f_2903_);
                    crate::leanh::lean_inc(v_subFn_x3f_2902_);
                    crate::leanh::lean_inc(v_mulFn_x3f_2901_);
                    crate::leanh::lean_inc(v_addFn_x3f_2900_);
                    crate::leanh::lean_inc(v_charInst_x3f_2899_);
                    crate::leanh::lean_inc(v_semiringInst_2898_);
                    crate::leanh::lean_inc(v_ringInst_2897_);
                    crate::leanh::lean_inc(v_u_2896_);
                    crate::leanh::lean_inc(v_type_2895_);
                    crate::leanh::lean_inc(v_id_2894_);
                    crate::leanh::lean_dec(v_toRing_2872_);
                    v___x_2911_ = crate::leanh::lean_box(0);
                    v_isShared_2912_ = v_isSharedCheck_2920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2913_, 0, v_a_2870_);
                if v_isShared_2912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2911_, 9, v___x_2913_);
                    v___x_2915_ = v___x_2911_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2919_ = crate::leanh::lean_alloc_ctor(0, 17, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_id_2894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_type_2895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_u_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_ringInst_2897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 4, v_semiringInst_2898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 5, v_charInst_x3f_2899_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 6, v_addFn_x3f_2900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 7, v_mulFn_x3f_2901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 8, v_subFn_x3f_2902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 9, v___x_2913_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 10, v_powFn_x3f_2903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 11, v_intCastFn_x3f_2904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 12, v_natCastFn_x3f_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 13, v_one_x3f_2906_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 14, v_vars_2907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 15, v_varMap_2908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 16, v_denote_2909_);
                    v___x_2915_ = v_reuseFailAlloc_2919_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2893_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2892_, 0, v___x_2915_);
                    v___x_2917_ = v___x_2892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = crate::leanh::lean_alloc_ctor(0, 17, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_invFn_x3f_2873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_semiringId_x3f_2874_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2918_,
                        3,
                        v_commSemiringInst_2875_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_commRingInst_2876_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2918_,
                        5,
                        v_noZeroDivInst_x3f_2877_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 6, v_fieldInst_x3f_2878_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2918_,
                        7,
                        v_powIdentityInst_x3f_2879_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 8, v_denoteEntries_2880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 9, v_nextId_2881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 10, v_steps_2882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 11, v_queue_2883_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 12, v_basis_2884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 13, v_diseqs_2885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 14, v_invSet_2887_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2918_,
                        15,
                        v_powIdentityVarCount_2888_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2918_, 16, v_numEq0_x3f_2889_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2918_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_recheck_2886_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2918_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17 + 1) as u32,
                        v_numEq0Updated_2890_,
                    );
                    v___x_2917_ = v_reuseFailAlloc_2918_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2(
    mut v_type_2923_: *mut crate::leanh::LeanObject,
    mut v_u_2924_: *mut crate::leanh::LeanObject,
    mut v_instDeclName_2925_: *mut crate::leanh::LeanObject,
    mut v_declName_2926_: *mut crate::leanh::LeanObject,
    mut v_expectedInst_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
    mut v___y_2930_: *mut crate::leanh::LeanObject,
    mut v___y_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2940_ = crate::leanh::lean_box(0);
                v___x_2941_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2941_, 0, v_u_2924_);
                crate::leanh::lean_ctor_set(v___x_2941_, 1, v___x_2940_);
                crate::leanh::lean_inc_ref(v___x_2941_);
                v___x_2942_ = l_Lean_mkConst(v_instDeclName_2925_, v___x_2941_);
                crate::leanh::lean_inc_ref(v_type_2923_);
                v___x_2943_ = l_Lean_Expr_app___override(v___x_2942_, v_type_2923_);
                v___x_2944_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5(v___x_2943_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
                if crate::leanh::lean_obj_tag(v___x_2944_) == 0 {
                    v_a_2945_ = crate::leanh::lean_ctor_get(v___x_2944_, 0);
                    crate::leanh::lean_inc_n(v_a_2945_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2944_, 1);
                    crate::leanh::lean_inc(v_declName_2926_);
                    v___x_2946_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(
                        v_declName_2926_,
                        v_a_2945_,
                        v_expectedInst_2927_,
                        v___y_2935_,
                        v___y_2936_,
                        v___y_2937_,
                        v___y_2938_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2946_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2946_, 1);
                        v___x_2947_ = l_Lean_mkConst(v_declName_2926_, v___x_2941_);
                        v___x_2948_ = l_Lean_mkAppB(v___x_2947_, v_type_2923_, v_a_2945_);
                        v___x_2949_ = l_Lean_Meta_Sym_canon(
                            v___x_2948_,
                            v___y_2933_,
                            v___y_2934_,
                            v___y_2935_,
                            v___y_2936_,
                            v___y_2937_,
                            v___y_2938_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2949_) == 0 {
                            v_a_2950_ = crate::leanh::lean_ctor_get(v___x_2949_, 0);
                            crate::leanh::lean_inc(v_a_2950_);
                            crate::leanh::lean_dec_ref_known(v___x_2949_, 1);
                            v___x_2951_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_2950_, v___y_2934_);
                            return v___x_2951_;
                        } else {
                            return v___x_2949_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2945_);
                        crate::leanh::lean_dec_ref_known(v___x_2941_, 2);
                        crate::leanh::lean_dec(v_declName_2926_);
                        crate::leanh::lean_dec_ref(v_type_2923_);
                        v_a_2952_ = crate::leanh::lean_ctor_get(v___x_2946_, 0);
                        v_isSharedCheck_2959_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2946_)) as u8;
                        if v_isSharedCheck_2959_ == 0 {
                            v___x_2954_ = v___x_2946_;
                            v_isShared_2955_ = v_isSharedCheck_2959_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2952_);
                            crate::leanh::lean_dec(v___x_2946_);
                            v___x_2954_ = crate::leanh::lean_box(0);
                            v_isShared_2955_ = v_isSharedCheck_2959_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2941_, 2);
                    crate::leanh::lean_dec_ref(v_expectedInst_2927_);
                    crate::leanh::lean_dec(v_declName_2926_);
                    crate::leanh::lean_dec_ref(v_type_2923_);
                    return v___x_2944_;
                }
            }
            1 => {
                if v_isShared_2955_ == 0 {
                    v___x_2957_ = v___x_2954_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
                    v___x_2957_ = v_reuseFailAlloc_2958_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_2960_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_u_2961_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_instDeclName_2962_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_declName_2963_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_expectedInst_2964_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_2965_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_2966_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_2967_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_2968_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_2969_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_2970_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_2971_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_2972_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_2973_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_2974_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_2975_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_2976_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2(v_type_2960_, v_u_2961_, v_instDeclName_2962_, v_declName_2963_, v_expectedInst_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
    crate::leanh::lean_dec(v___y_2975_);
    crate::leanh::lean_dec_ref(v___y_2974_);
    crate::leanh::lean_dec(v___y_2973_);
    crate::leanh::lean_dec_ref(v___y_2972_);
    crate::leanh::lean_dec(v___y_2971_);
    crate::leanh::lean_dec_ref(v___y_2970_);
    crate::leanh::lean_dec(v___y_2969_);
    crate::leanh::lean_dec_ref(v___y_2968_);
    crate::leanh::lean_dec(v___y_2967_);
    crate::leanh::lean_dec(v___y_2966_);
    crate::leanh::lean_dec(v___y_2965_);
    return v_res_2977_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1(
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
    mut v___y_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v_negFn_x3f_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedInst_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut v_unused_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3043_: u8 = 0;
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3056_: u8 = 0;
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut v_a_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3065_: u8 = 0;
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3004_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
                    v___y_2992_,
                    v___y_2993_,
                    v___y_2994_,
                    v___y_2995_,
                    v___y_2996_,
                    v___y_2997_,
                    v___y_2998_,
                    v___y_2999_,
                    v___y_3000_,
                    v___y_3001_,
                    v___y_3002_,
                );
                if crate::leanh::lean_obj_tag(v___x_3004_) == 0 {
                    v_a_3005_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                    v_isSharedCheck_3061_ = (!crate::leanh::lean_is_exclusive(v___x_3004_)) as u8;
                    if v_isSharedCheck_3061_ == 0 {
                        v___x_3007_ = v___x_3004_;
                        v_isShared_3008_ = v_isSharedCheck_3061_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3005_);
                        crate::leanh::lean_dec(v___x_3004_);
                        v___x_3007_ = crate::leanh::lean_box(0);
                        v_isShared_3008_ = v_isSharedCheck_3061_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3062_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                    v_isSharedCheck_3069_ = (!crate::leanh::lean_is_exclusive(v___x_3004_)) as u8;
                    if v_isSharedCheck_3069_ == 0 {
                        v___x_3064_ = v___x_3004_;
                        v_isShared_3065_ = v_isSharedCheck_3069_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3062_);
                        crate::leanh::lean_dec(v___x_3004_);
                        v___x_3064_ = crate::leanh::lean_box(0);
                        v_isShared_3065_ = v_isSharedCheck_3069_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_negFn_x3f_3009_ = crate::leanh::lean_ctor_get(v_a_3005_, 9);
                if crate::leanh::lean_obj_tag(v_negFn_x3f_3009_) == 1 {
                    crate::leanh::lean_inc_ref(v_negFn_x3f_3009_);
                    crate::leanh::lean_dec(v_a_3005_);
                    v_val_3010_ = crate::leanh::lean_ctor_get(v_negFn_x3f_3009_, 0);
                    crate::leanh::lean_inc(v_val_3010_);
                    crate::leanh::lean_dec_ref_known(v_negFn_x3f_3009_, 1);
                    if v_isShared_3008_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3007_, 0, v_val_3010_);
                        v___x_3012_ = v___x_3007_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3013_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_val_3010_);
                        v___x_3012_ = v_reuseFailAlloc_3013_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3007_);
                    v_type_3014_ = crate::leanh::lean_ctor_get(v_a_3005_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_3014_, 2);
                    v_u_3015_ = crate::leanh::lean_ctor_get(v_a_3005_, 2);
                    crate::leanh::lean_inc_n(v_u_3015_, 2);
                    v_ringInst_3016_ = crate::leanh::lean_ctor_get(v_a_3005_, 3);
                    crate::leanh::lean_inc_ref(v_ringInst_3016_);
                    crate::leanh::lean_dec(v_a_3005_);
                    v___x_3017_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__2;
                    v___x_3018_ = crate::leanh::lean_box(0);
                    v___x_3019_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3019_, 0, v_u_3015_);
                    crate::leanh::lean_ctor_set(v___x_3019_, 1, v___x_3018_);
                    v___x_3020_ = l_Lean_mkConst(v___x_3017_, v___x_3019_);
                    v_expectedInst_3021_ =
                        l_Lean_mkAppB(v___x_3020_, v_type_3014_, v_ringInst_3016_);
                    v___x_3022_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__4;
                    v___x_3023_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___closed__6;
                    v___x_3024_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2(v_type_3014_, v_u_3015_, v___x_3022_, v___x_3023_, v_expectedInst_3021_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
                    if crate::leanh::lean_obj_tag(v___x_3024_) == 0 {
                        v_a_3025_ = crate::leanh::lean_ctor_get(v___x_3024_, 0);
                        crate::leanh::lean_inc(v_a_3025_);
                        crate::leanh::lean_dec_ref_known(v___x_3024_, 1);
                        v___x_3044_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v___y_2992_,
                            v___y_2993_,
                            v___y_2994_,
                            v___y_2995_,
                            v___y_2996_,
                            v___y_2997_,
                            v___y_2998_,
                            v___y_2999_,
                            v___y_3000_,
                            v___y_3001_,
                            v___y_3002_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3044_) == 0 {
                            v_a_3045_ = crate::leanh::lean_ctor_get(v___x_3044_, 0);
                            crate::leanh::lean_inc(v_a_3045_);
                            crate::leanh::lean_dec_ref_known(v___x_3044_, 1);
                            v_ringId_x3f_3046_ = crate::leanh::lean_ctor_get(v_a_3045_, 1);
                            crate::leanh::lean_inc(v_ringId_x3f_3046_);
                            crate::leanh::lean_dec(v_a_3045_);
                            if crate::leanh::lean_obj_tag(v_ringId_x3f_3046_) == 1 {
                                v_val_3047_ = crate::leanh::lean_ctor_get(v_ringId_x3f_3046_, 0);
                                crate::leanh::lean_inc(v_val_3047_);
                                crate::leanh::lean_dec_ref_known(v_ringId_x3f_3046_, 1);
                                crate::leanh::lean_inc(v_a_3025_);
                                v___f_3048_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___lam__0 as *mut core::ffi::c_void, 2, 1);
                                crate::leanh::lean_closure_set(v___f_3048_, 0, v_a_3025_);
                                v___x_3049_ = 0;
                                v___x_3050_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3050_, 0, v_val_3047_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3050_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                    v___x_3049_,
                                );
                                v___x_3051_ =
                                    l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(
                                        v___f_3048_,
                                        v___x_3050_,
                                        v___y_2993_,
                                    );
                                crate::leanh::lean_dec_ref_known(v___x_3050_, 1);
                                v___y_3027_ = v___x_3051_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_ringId_x3f_3046_);
                                v___x_3052_ =
                                    l_Lean_Meta_Grind_Arith_Linear_throwNotCommRing___redArg(
                                        v___y_2999_,
                                        v___y_3000_,
                                        v___y_3001_,
                                        v___y_3002_,
                                    );
                                v___y_3027_ = v___x_3052_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3025_);
                            v_a_3053_ = crate::leanh::lean_ctor_get(v___x_3044_, 0);
                            v_isSharedCheck_3060_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3044_)) as u8;
                            if v_isSharedCheck_3060_ == 0 {
                                v___x_3055_ = v___x_3044_;
                                v_isShared_3056_ = v_isSharedCheck_3060_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3053_);
                                crate::leanh::lean_dec(v___x_3044_);
                                v___x_3055_ = crate::leanh::lean_box(0);
                                v_isShared_3056_ = v_isSharedCheck_3060_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        return v___x_3024_;
                    }
                }
            }
            2 => {
                return v___x_3012_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___y_3027_) == 0 {
                    v_isSharedCheck_3034_ = (!crate::leanh::lean_is_exclusive(v___y_3027_)) as u8;
                    if v_isSharedCheck_3034_ == 0 {
                        v_unused_3035_ = crate::leanh::lean_ctor_get(v___y_3027_, 0);
                        crate::leanh::lean_dec(v_unused_3035_);
                        v___x_3029_ = v___y_3027_;
                        v_isShared_3030_ = v_isSharedCheck_3034_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_3027_);
                        v___x_3029_ = crate::leanh::lean_box(0);
                        v_isShared_3030_ = v_isSharedCheck_3034_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3025_);
                    v_a_3036_ = crate::leanh::lean_ctor_get(v___y_3027_, 0);
                    v_isSharedCheck_3043_ = (!crate::leanh::lean_is_exclusive(v___y_3027_)) as u8;
                    if v_isSharedCheck_3043_ == 0 {
                        v___x_3038_ = v___y_3027_;
                        v_isShared_3039_ = v_isSharedCheck_3043_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3036_);
                        crate::leanh::lean_dec(v___y_3027_);
                        v___x_3038_ = crate::leanh::lean_box(0);
                        v_isShared_3039_ = v_isSharedCheck_3043_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3030_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3029_, 0, v_a_3025_);
                    v___x_3032_ = v___x_3029_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3025_);
                    v___x_3032_ = v_reuseFailAlloc_3033_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3032_;
            }
            6 => {
                if v_isShared_3039_ == 0 {
                    v___x_3041_ = v___x_3038_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3042_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
                    v___x_3041_ = v_reuseFailAlloc_3042_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3041_;
            }
            8 => {
                if v_isShared_3056_ == 0 {
                    v___x_3058_ = v___x_3055_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
                    v___x_3058_ = v_reuseFailAlloc_3059_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3058_;
            }
            10 => {
                if v_isShared_3065_ == 0 {
                    v___x_3067_ = v___x_3064_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3068_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
                    v___x_3067_ = v_reuseFailAlloc_3068_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1___boxed(
    mut v___y_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
    mut v___y_3079_: *mut crate::leanh::LeanObject,
    mut v___y_3080_: *mut crate::leanh::LeanObject,
    mut v___y_3081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3082_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1(v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
    crate::leanh::lean_dec(v___y_3080_);
    crate::leanh::lean_dec_ref(v___y_3079_);
    crate::leanh::lean_dec(v___y_3078_);
    crate::leanh::lean_dec_ref(v___y_3077_);
    crate::leanh::lean_dec(v___y_3076_);
    crate::leanh::lean_dec_ref(v___y_3075_);
    crate::leanh::lean_dec(v___y_3074_);
    crate::leanh::lean_dec_ref(v___y_3073_);
    crate::leanh::lean_dec(v___y_3072_);
    crate::leanh::lean_dec(v___y_3071_);
    crate::leanh::lean_dec(v___y_3070_);
    return v_res_3082_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3091_ = lean_nat_to_int(v___x_3090_);
    return v___x_3091_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0(
    mut v_k_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
    mut v___y_3101_: *mut crate::leanh::LeanObject,
    mut v___y_3102_: *mut crate::leanh::LeanObject,
    mut v___y_3103_: *mut crate::leanh::LeanObject,
    mut v___y_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v_ofNatInst_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3158_: u8 = 0;
    let mut v_val_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3163_: u8 = 0;
    let mut v_a_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3167_: u8 = 0;
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3171_: u8 = 0;
    let mut v_a_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3175_: u8 = 0;
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3110_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getRing(
                    v___y_3098_,
                    v___y_3099_,
                    v___y_3100_,
                    v___y_3101_,
                    v___y_3102_,
                    v___y_3103_,
                    v___y_3104_,
                    v___y_3105_,
                    v___y_3106_,
                    v___y_3107_,
                    v___y_3108_,
                );
                if crate::leanh::lean_obj_tag(v___x_3110_) == 0 {
                    v_a_3111_ = crate::leanh::lean_ctor_get(v___x_3110_, 0);
                    crate::leanh::lean_inc(v_a_3111_);
                    crate::leanh::lean_dec_ref_known(v___x_3110_, 1);
                    v_type_3112_ = crate::leanh::lean_ctor_get(v_a_3111_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_3112_, 2);
                    v_u_3113_ = crate::leanh::lean_ctor_get(v_a_3111_, 2);
                    crate::leanh::lean_inc(v_u_3113_);
                    v_semiringInst_3114_ = crate::leanh::lean_ctor_get(v_a_3111_, 4);
                    crate::leanh::lean_inc_ref(v_semiringInst_3114_);
                    crate::leanh::lean_dec(v_a_3111_);
                    v___x_3115_ = lean_nat_abs(v_k_3097_);
                    v_n_3116_ = l_Lean_mkRawNatLit(v___x_3115_);
                    v___x_3117_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__1;
                    v___x_3118_ = crate::leanh::lean_box(0);
                    v___x_3119_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3119_, 0, v_u_3113_);
                    crate::leanh::lean_ctor_set(v___x_3119_, 1, v___x_3118_);
                    crate::leanh::lean_inc_ref(v___x_3119_);
                    v___x_3120_ = l_Lean_mkConst(v___x_3117_, v___x_3119_);
                    crate::leanh::lean_inc_ref(v_n_3116_);
                    v___x_3121_ = l_Lean_mkAppB(v___x_3120_, v_type_3112_, v_n_3116_);
                    v___x_3122_ = crate::leanh::lean_box(0);
                    v___x_3123_ = l_Lean_Meta_synthInstance_x3f(
                        v___x_3121_,
                        v___x_3122_,
                        v___y_3105_,
                        v___y_3106_,
                        v___y_3107_,
                        v___y_3108_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3123_) == 0 {
                        v_a_3124_ = crate::leanh::lean_ctor_get(v___x_3123_, 0);
                        v_isSharedCheck_3163_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3123_)) as u8;
                        if v_isSharedCheck_3163_ == 0 {
                            v___x_3126_ = v___x_3123_;
                            v_isShared_3127_ = v_isSharedCheck_3163_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3124_);
                            crate::leanh::lean_dec(v___x_3123_);
                            v___x_3126_ = crate::leanh::lean_box(0);
                            v_isShared_3127_ = v_isSharedCheck_3163_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_3119_, 2);
                        crate::leanh::lean_dec_ref(v_n_3116_);
                        crate::leanh::lean_dec_ref(v_semiringInst_3114_);
                        crate::leanh::lean_dec_ref(v_type_3112_);
                        v_a_3164_ = crate::leanh::lean_ctor_get(v___x_3123_, 0);
                        v_isSharedCheck_3171_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3123_)) as u8;
                        if v_isSharedCheck_3171_ == 0 {
                            v___x_3166_ = v___x_3123_;
                            v_isShared_3167_ = v_isSharedCheck_3171_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3164_);
                            crate::leanh::lean_dec(v___x_3123_);
                            v___x_3166_ = crate::leanh::lean_box(0);
                            v_isShared_3167_ = v_isSharedCheck_3171_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_3172_ = crate::leanh::lean_ctor_get(v___x_3110_, 0);
                    v_isSharedCheck_3179_ = (!crate::leanh::lean_is_exclusive(v___x_3110_)) as u8;
                    if v_isSharedCheck_3179_ == 0 {
                        v___x_3174_ = v___x_3110_;
                        v_isShared_3175_ = v_isSharedCheck_3179_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3172_);
                        crate::leanh::lean_dec(v___x_3110_);
                        v___x_3174_ = crate::leanh::lean_box(0);
                        v_isShared_3175_ = v_isSharedCheck_3179_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3124_) == 1 {
                    crate::leanh::lean_dec_ref(v_semiringInst_3114_);
                    v_val_3159_ = crate::leanh::lean_ctor_get(v_a_3124_, 0);
                    crate::leanh::lean_inc(v_val_3159_);
                    crate::leanh::lean_dec_ref_known(v_a_3124_, 1);
                    v_ofNatInst_3129_ = v_val_3159_;
                    v___y_3130_ = v___y_3098_;
                    v___y_3131_ = v___y_3099_;
                    v___y_3132_ = v___y_3100_;
                    v___y_3133_ = v___y_3101_;
                    v___y_3134_ = v___y_3102_;
                    v___y_3135_ = v___y_3103_;
                    v___y_3136_ = v___y_3104_;
                    v___y_3137_ = v___y_3105_;
                    v___y_3138_ = v___y_3106_;
                    v___y_3139_ = v___y_3107_;
                    v___y_3140_ = v___y_3108_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_3124_);
                    v___x_3160_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__5;
                    crate::leanh::lean_inc_ref(v___x_3119_);
                    v___x_3161_ = l_Lean_mkConst(v___x_3160_, v___x_3119_);
                    crate::leanh::lean_inc_ref(v_n_3116_);
                    crate::leanh::lean_inc_ref(v_type_3112_);
                    v___x_3162_ =
                        l_Lean_mkApp3(v___x_3161_, v_type_3112_, v_semiringInst_3114_, v_n_3116_);
                    v_ofNatInst_3129_ = v___x_3162_;
                    v___y_3130_ = v___y_3098_;
                    v___y_3131_ = v___y_3099_;
                    v___y_3132_ = v___y_3100_;
                    v___y_3133_ = v___y_3101_;
                    v___y_3134_ = v___y_3102_;
                    v___y_3135_ = v___y_3103_;
                    v___y_3136_ = v___y_3104_;
                    v___y_3137_ = v___y_3105_;
                    v___y_3138_ = v___y_3106_;
                    v___y_3139_ = v___y_3107_;
                    v___y_3140_ = v___y_3108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3141_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__3;
                v___x_3142_ = l_Lean_mkConst(v___x_3141_, v___x_3119_);
                v_n_3143_ = l_Lean_mkApp3(v___x_3142_, v_type_3112_, v_n_3116_, v_ofNatInst_3129_);
                v___x_3144_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__4_once), _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___closed__4);
                v___x_3145_ = lean_int_dec_lt(v_k_3097_, v___x_3144_);
                if v___x_3145_ == 0 {
                    if v_isShared_3127_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3126_, 0, v_n_3143_);
                        v___x_3147_ = v___x_3126_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_n_3143_);
                        v___x_3147_ = v_reuseFailAlloc_3148_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3126_);
                    v___x_3149_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1(v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
                    if crate::leanh::lean_obj_tag(v___x_3149_) == 0 {
                        v_a_3150_ = crate::leanh::lean_ctor_get(v___x_3149_, 0);
                        v_isSharedCheck_3158_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3149_)) as u8;
                        if v_isSharedCheck_3158_ == 0 {
                            v___x_3152_ = v___x_3149_;
                            v_isShared_3153_ = v_isSharedCheck_3158_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3150_);
                            crate::leanh::lean_dec(v___x_3149_);
                            v___x_3152_ = crate::leanh::lean_box(0);
                            v_isShared_3153_ = v_isSharedCheck_3158_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_n_3143_);
                        return v___x_3149_;
                    }
                }
            }
            3 => {
                return v___x_3147_;
            }
            4 => {
                v___x_3154_ = l_Lean_Expr_app___override(v_a_3150_, v_n_3143_);
                if v_isShared_3153_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3152_, 0, v___x_3154_);
                    v___x_3156_ = v___x_3152_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3154_);
                    v___x_3156_ = v_reuseFailAlloc_3157_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3156_;
            }
            6 => {
                if v_isShared_3167_ == 0 {
                    v___x_3169_ = v___x_3166_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
                    v___x_3169_ = v_reuseFailAlloc_3170_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3169_;
            }
            8 => {
                if v_isShared_3175_ == 0 {
                    v___x_3177_ = v___x_3174_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0___boxed(
    mut v_k_3180_: *mut crate::leanh::LeanObject,
    mut v___y_3181_: *mut crate::leanh::LeanObject,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
    mut v___y_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
    mut v___y_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
    mut v___y_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3193_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0(v_k_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
    crate::leanh::lean_dec(v___y_3191_);
    crate::leanh::lean_dec_ref(v___y_3190_);
    crate::leanh::lean_dec(v___y_3189_);
    crate::leanh::lean_dec_ref(v___y_3188_);
    crate::leanh::lean_dec(v___y_3187_);
    crate::leanh::lean_dec_ref(v___y_3186_);
    crate::leanh::lean_dec(v___y_3185_);
    crate::leanh::lean_dec_ref(v___y_3184_);
    crate::leanh::lean_dec(v___y_3183_);
    crate::leanh::lean_dec(v___y_3182_);
    crate::leanh::lean_dec(v___y_3181_);
    crate::leanh::lean_dec(v_k_3180_);
    return v_res_3193_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0(
    mut v_m_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_3194_) == 0 {
        let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3207_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Grind_Linarith_Poly_denoteExpr_denoteTerm___redArg___closed__0);
        v___x_3208_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0(v___x_3207_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
        return v___x_3208_;
    } else {
        let mut v_p_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_3209_ = crate::leanh::lean_ctor_get(v_m_3194_, 0);
        crate::leanh::lean_inc_ref(v_p_3209_);
        v_m_3210_ = crate::leanh::lean_ctor_get(v_m_3194_, 1);
        crate::leanh::lean_inc(v_m_3210_);
        crate::leanh::lean_dec_ref_known(v_m_3194_, 2);
        v___x_3211_ = l_Lean_Grind_CommRing_Power_denoteExpr___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__1(v_p_3209_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
        if crate::leanh::lean_obj_tag(v___x_3211_) == 0 {
            let mut v_a_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_3212_ = crate::leanh::lean_ctor_get(v___x_3211_, 0);
            crate::leanh::lean_inc(v_a_3212_);
            crate::leanh::lean_dec_ref_known(v___x_3211_, 1);
            v___x_3213_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr_0__Lean_Grind_CommRing_Mon_denoteExpr_go___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__2(v_m_3210_, v_a_3212_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
            return v___x_3213_;
        } else {
            crate::leanh::lean_dec(v_m_3210_);
            return v___x_3211_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0___boxed(
    mut v_m_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
    mut v___y_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
    mut v___y_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3227_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0(v_m_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
    crate::leanh::lean_dec(v___y_3225_);
    crate::leanh::lean_dec_ref(v___y_3224_);
    crate::leanh::lean_dec(v___y_3223_);
    crate::leanh::lean_dec_ref(v___y_3222_);
    crate::leanh::lean_dec(v___y_3221_);
    crate::leanh::lean_dec_ref(v___y_3220_);
    crate::leanh::lean_dec(v___y_3219_);
    crate::leanh::lean_dec_ref(v___y_3218_);
    crate::leanh::lean_dec(v___y_3217_);
    crate::leanh::lean_dec(v___y_3216_);
    crate::leanh::lean_dec(v___y_3215_);
    return v_res_3227_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr(
    mut v_p_3228_: *mut crate::leanh::LeanObject,
    mut v_a_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
    mut v_a_3238_: *mut crate::leanh::LeanObject,
    mut v_a_3239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v_addFn_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_a_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v_a_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3277_: u8 = 0;
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_3228_) == 0 {
                    v_k_3241_ = crate::leanh::lean_ctor_get(v_p_3228_, 0);
                    crate::leanh::lean_inc(v_k_3241_);
                    crate::leanh::lean_dec_ref_known(v_p_3228_, 1);
                    v___x_3242_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr_0__Lean_Meta_Grind_Arith_Linear_denoteNum(v_k_3241_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
                    crate::leanh::lean_dec(v_k_3241_);
                    return v___x_3242_;
                } else {
                    v_k_3243_ = crate::leanh::lean_ctor_get(v_p_3228_, 0);
                    crate::leanh::lean_inc(v_k_3243_);
                    v_v_3244_ = crate::leanh::lean_ctor_get(v_p_3228_, 1);
                    crate::leanh::lean_inc(v_v_3244_);
                    v_p_3245_ = crate::leanh::lean_ctor_get(v_p_3228_, 2);
                    crate::leanh::lean_inc_ref(v_p_3245_);
                    crate::leanh::lean_dec_ref_known(v_p_3228_, 3);
                    v___x_3246_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_,
                        v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3246_) == 0 {
                        v_a_3247_ = crate::leanh::lean_ctor_get(v___x_3246_, 0);
                        crate::leanh::lean_inc(v_a_3247_);
                        crate::leanh::lean_dec_ref_known(v___x_3246_, 1);
                        v___x_3248_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                            v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_,
                            v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3248_) == 0 {
                            v_a_3249_ = crate::leanh::lean_ctor_get(v___x_3248_, 0);
                            crate::leanh::lean_inc(v_a_3249_);
                            crate::leanh::lean_dec_ref_known(v___x_3248_, 1);
                            v___x_3250_ = l_Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0(v_v_3244_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
                            if crate::leanh::lean_obj_tag(v___x_3250_) == 0 {
                                v_a_3251_ = crate::leanh::lean_ctor_get(v___x_3250_, 0);
                                crate::leanh::lean_inc(v_a_3251_);
                                crate::leanh::lean_dec_ref_known(v___x_3250_, 1);
                                v___x_3252_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr(
                                    v_p_3245_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_,
                                    v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_,
                                    v_a_3238_, v_a_3239_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3252_) == 0 {
                                    v_a_3253_ = crate::leanh::lean_ctor_get(v___x_3252_, 0);
                                    v_isSharedCheck_3265_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3252_)) as u8;
                                    if v_isSharedCheck_3265_ == 0 {
                                        v___x_3255_ = v___x_3252_;
                                        v_isShared_3256_ = v_isSharedCheck_3265_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3253_);
                                        crate::leanh::lean_dec(v___x_3252_);
                                        v___x_3255_ = crate::leanh::lean_box(0);
                                        v_isShared_3256_ = v_isSharedCheck_3265_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3251_);
                                    crate::leanh::lean_dec(v_a_3249_);
                                    crate::leanh::lean_dec(v_a_3247_);
                                    crate::leanh::lean_dec(v_k_3243_);
                                    return v___x_3252_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3249_);
                                crate::leanh::lean_dec(v_a_3247_);
                                crate::leanh::lean_dec_ref(v_p_3245_);
                                crate::leanh::lean_dec(v_k_3243_);
                                return v___x_3250_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3247_);
                            crate::leanh::lean_dec_ref(v_p_3245_);
                            crate::leanh::lean_dec(v_v_3244_);
                            crate::leanh::lean_dec(v_k_3243_);
                            v_a_3266_ = crate::leanh::lean_ctor_get(v___x_3248_, 0);
                            v_isSharedCheck_3273_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3248_)) as u8;
                            if v_isSharedCheck_3273_ == 0 {
                                v___x_3268_ = v___x_3248_;
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3266_);
                                crate::leanh::lean_dec(v___x_3248_);
                                v___x_3268_ = crate::leanh::lean_box(0);
                                v_isShared_3269_ = v_isSharedCheck_3273_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_p_3245_);
                        crate::leanh::lean_dec(v_v_3244_);
                        crate::leanh::lean_dec(v_k_3243_);
                        v_a_3274_ = crate::leanh::lean_ctor_get(v___x_3246_, 0);
                        v_isSharedCheck_3281_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3246_)) as u8;
                        if v_isSharedCheck_3281_ == 0 {
                            v___x_3276_ = v___x_3246_;
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3274_);
                            crate::leanh::lean_dec(v___x_3246_);
                            v___x_3276_ = crate::leanh::lean_box(0);
                            v_isShared_3277_ = v_isSharedCheck_3281_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_addFn_3257_ = crate::leanh::lean_ctor_get(v_a_3247_, 22);
                crate::leanh::lean_inc_ref(v_addFn_3257_);
                crate::leanh::lean_dec(v_a_3247_);
                v_zsmulFn_3258_ = crate::leanh::lean_ctor_get(v_a_3249_, 23);
                crate::leanh::lean_inc_ref(v_zsmulFn_3258_);
                crate::leanh::lean_dec(v_a_3249_);
                v___x_3259_ = l_Lean_mkIntLit(v_k_3243_);
                crate::leanh::lean_dec(v_k_3243_);
                v___x_3260_ = l_Lean_mkAppB(v_zsmulFn_3258_, v___x_3259_, v_a_3251_);
                v___x_3261_ = l_Lean_mkAppB(v_addFn_3257_, v___x_3260_, v_a_3253_);
                if v_isShared_3256_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3261_);
                    v___x_3263_ = v___x_3255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3263_;
            }
            3 => {
                if v_isShared_3269_ == 0 {
                    v___x_3271_ = v___x_3268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
                    v___x_3271_ = v_reuseFailAlloc_3272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3271_;
            }
            5 => {
                if v_isShared_3277_ == 0 {
                    v___x_3279_ = v___x_3276_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
                    v___x_3279_ = v_reuseFailAlloc_3280_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr___boxed(
    mut v_p_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
    mut v_a_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
    mut v_a_3289_: *mut crate::leanh::LeanObject,
    mut v_a_3290_: *mut crate::leanh::LeanObject,
    mut v_a_3291_: *mut crate::leanh::LeanObject,
    mut v_a_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr(
        v_p_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_,
        v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_,
    );
    crate::leanh::lean_dec(v_a_3293_);
    crate::leanh::lean_dec_ref(v_a_3292_);
    crate::leanh::lean_dec(v_a_3291_);
    crate::leanh::lean_dec_ref(v_a_3290_);
    crate::leanh::lean_dec(v_a_3289_);
    crate::leanh::lean_dec_ref(v_a_3288_);
    crate::leanh::lean_dec(v_a_3287_);
    crate::leanh::lean_dec_ref(v_a_3286_);
    crate::leanh::lean_dec(v_a_3285_);
    crate::leanh::lean_dec(v_a_3284_);
    crate::leanh::lean_dec(v_a_3283_);
    return v_res_3295_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8(
    mut v_00_u03b1_3296_: *mut crate::leanh::LeanObject,
    mut v_msg_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___y_3302_: *mut crate::leanh::LeanObject,
    mut v___y_3303_: *mut crate::leanh::LeanObject,
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3310_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8___redArg(v_msg_3297_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
    return v___x_3310_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8___boxed(
    mut v_00_u03b1_3311_: *mut crate::leanh::LeanObject,
    mut v_msg_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
    mut v___y_3318_: *mut crate::leanh::LeanObject,
    mut v___y_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3325_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00Lean_Grind_CommRing_Mon_denoteExpr___at___00Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr_spec__0_spec__0_spec__1_spec__2_spec__5_spec__8(v_00_u03b1_3311_, v_msg_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
    crate::leanh::lean_dec(v___y_3323_);
    crate::leanh::lean_dec_ref(v___y_3322_);
    crate::leanh::lean_dec(v___y_3321_);
    crate::leanh::lean_dec_ref(v___y_3320_);
    crate::leanh::lean_dec(v___y_3319_);
    crate::leanh::lean_dec_ref(v___y_3318_);
    crate::leanh::lean_dec(v___y_3317_);
    crate::leanh::lean_dec_ref(v___y_3316_);
    crate::leanh::lean_dec(v___y_3315_);
    crate::leanh::lean_dec(v___y_3314_);
    crate::leanh::lean_dec(v___y_3313_);
    return v_res_3325_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_toIntModuleExpr___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Lean_Meta_Grind_Arith_getIntModuleVirtualParent;
    v___x_3327_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3327_, 0, v___x_3326_);
    return v___x_3327_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_toIntModuleExpr(
    mut v_p_3328_: *mut crate::leanh::LeanObject,
    mut v_generation_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
    mut v_a_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3350_: u8 = 0;
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3354_: u8 = 0;
    let mut v_unused_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3363_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3342_ = l_Lean_Grind_CommRing_Poly_denoteAsIntModuleExpr(
                    v_p_3328_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_,
                    v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_,
                );
                if crate::leanh::lean_obj_tag(v___x_3342_) == 0 {
                    v_a_3343_ = crate::leanh::lean_ctor_get(v___x_3342_, 0);
                    crate::leanh::lean_inc(v_a_3343_);
                    crate::leanh::lean_dec_ref_known(v___x_3342_, 1);
                    v___x_3344_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                        v_a_3343_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_,
                        v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3344_) == 0 {
                        v_a_3345_ = crate::leanh::lean_ctor_get(v___x_3344_, 0);
                        crate::leanh::lean_inc_n(v_a_3345_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3344_, 1);
                        v___x_3346_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_Poly_toIntModuleExpr___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Grind_CommRing_Poly_toIntModuleExpr___closed__0_once
                            ),
                            _init_l_Lean_Grind_CommRing_Poly_toIntModuleExpr___closed__0,
                        );
                        crate::leanh::lean_inc(v_a_3340_);
                        crate::leanh::lean_inc_ref(v_a_3339_);
                        crate::leanh::lean_inc(v_a_3338_);
                        crate::leanh::lean_inc_ref(v_a_3337_);
                        crate::leanh::lean_inc(v_a_3336_);
                        crate::leanh::lean_inc_ref(v_a_3335_);
                        crate::leanh::lean_inc(v_a_3334_);
                        crate::leanh::lean_inc_ref(v_a_3333_);
                        crate::leanh::lean_inc(v_a_3332_);
                        crate::leanh::lean_inc(v_a_3331_);
                        v___x_3347_ = lean_grind_internalize(
                            v_a_3345_,
                            v_generation_3329_,
                            v___x_3346_,
                            v_a_3331_,
                            v_a_3332_,
                            v_a_3333_,
                            v_a_3334_,
                            v_a_3335_,
                            v_a_3336_,
                            v_a_3337_,
                            v_a_3338_,
                            v_a_3339_,
                            v_a_3340_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3347_) == 0 {
                            v_isSharedCheck_3354_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3347_)) as u8;
                            if v_isSharedCheck_3354_ == 0 {
                                v_unused_3355_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                                crate::leanh::lean_dec(v_unused_3355_);
                                v___x_3349_ = v___x_3347_;
                                v_isShared_3350_ = v_isSharedCheck_3354_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3347_);
                                v___x_3349_ = crate::leanh::lean_box(0);
                                v_isShared_3350_ = v_isSharedCheck_3354_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3345_);
                            v_a_3356_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                            v_isSharedCheck_3363_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3347_)) as u8;
                            if v_isSharedCheck_3363_ == 0 {
                                v___x_3358_ = v___x_3347_;
                                v_isShared_3359_ = v_isSharedCheck_3363_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3356_);
                                crate::leanh::lean_dec(v___x_3347_);
                                v___x_3358_ = crate::leanh::lean_box(0);
                                v_isShared_3359_ = v_isSharedCheck_3363_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_generation_3329_);
                        return v___x_3344_;
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_3329_);
                    return v___x_3342_;
                }
            }
            1 => {
                if v_isShared_3350_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3349_, 0, v_a_3345_);
                    v___x_3352_ = v___x_3349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3345_);
                    v___x_3352_ = v_reuseFailAlloc_3353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3352_;
            }
            3 => {
                if v_isShared_3359_ == 0 {
                    v___x_3361_ = v___x_3358_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
                    v___x_3361_ = v_reuseFailAlloc_3362_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3361_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_toIntModuleExpr___boxed(
    mut v_p_3364_: *mut crate::leanh::LeanObject,
    mut v_generation_3365_: *mut crate::leanh::LeanObject,
    mut v_a_3366_: *mut crate::leanh::LeanObject,
    mut v_a_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
    mut v_a_3371_: *mut crate::leanh::LeanObject,
    mut v_a_3372_: *mut crate::leanh::LeanObject,
    mut v_a_3373_: *mut crate::leanh::LeanObject,
    mut v_a_3374_: *mut crate::leanh::LeanObject,
    mut v_a_3375_: *mut crate::leanh::LeanObject,
    mut v_a_3376_: *mut crate::leanh::LeanObject,
    mut v_a_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Lean_Grind_CommRing_Poly_toIntModuleExpr(
        v_p_3364_,
        v_generation_3365_,
        v_a_3366_,
        v_a_3367_,
        v_a_3368_,
        v_a_3369_,
        v_a_3370_,
        v_a_3371_,
        v_a_3372_,
        v_a_3373_,
        v_a_3374_,
        v_a_3375_,
        v_a_3376_,
    );
    crate::leanh::lean_dec(v_a_3376_);
    crate::leanh::lean_dec_ref(v_a_3375_);
    crate::leanh::lean_dec(v_a_3374_);
    crate::leanh::lean_dec_ref(v_a_3373_);
    crate::leanh::lean_dec(v_a_3372_);
    crate::leanh::lean_dec_ref(v_a_3371_);
    crate::leanh::lean_dec(v_a_3370_);
    crate::leanh::lean_dec_ref(v_a_3369_);
    crate::leanh::lean_dec(v_a_3368_);
    crate::leanh::lean_dec(v_a_3367_);
    crate::leanh::lean_dec(v_a_3366_);
    return v_res_3378_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
}
